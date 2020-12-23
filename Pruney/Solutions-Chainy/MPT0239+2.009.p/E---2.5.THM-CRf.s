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
% DateTime   : Thu Dec  3 10:39:27 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   52 (4552 expanded)
%              Number of clauses        :   37 (1953 expanded)
%              Number of leaves         :    7 (1231 expanded)
%              Depth                    :   14
%              Number of atoms          :  128 (11454 expanded)
%              Number of equality atoms :   65 (6960 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t77_enumset1,axiom,(
    ! [X1,X2] : k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(t79_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(t84_enumset1,axiom,(
    ! [X1,X2,X3] : k4_enumset1(X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
      <=> ( X1 = X3
          & X2 = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t34_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X15,X16] : k2_enumset1(X15,X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t77_enumset1])).

fof(c_0_10,plain,(
    ! [X17,X18,X19,X20] : k4_enumset1(X17,X17,X17,X18,X19,X20) = k2_enumset1(X17,X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t79_enumset1])).

fof(c_0_11,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0)))
      | esk2_0 != esk4_0
      | esk3_0 != esk5_0 )
    & ( esk2_0 = esk4_0
      | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0))) )
    & ( esk3_0 = esk5_0
      | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_12,plain,(
    ! [X14] : k1_enumset1(X14,X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] : k4_enumset1(X21,X21,X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t84_enumset1])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_enumset1(X1,X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0)))
    | esk2_0 != esk4_0
    | esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_enumset1(X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 = esk5_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( esk2_0 = esk4_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X24,X25,X26,X27] :
      ( ( r2_hidden(X24,X26)
        | ~ r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)) )
      & ( r2_hidden(X25,X27)
        | ~ r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)) )
      & ( ~ r2_hidden(X24,X26)
        | ~ r2_hidden(X25,X27)
        | r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X4,X4,X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 != esk2_0
    | esk5_0 != esk3_0
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = esk3_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 = esk2_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k4_enumset1(X3,X3,X3,X3,X3,X1),X4))
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_15]),c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | ~ r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X4,X4,X4,X4,X4,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).

cnf(c_0_36,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k4_enumset1(X1,X1,X1,X1,X1,X3),X4))
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

cnf(c_0_40,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k4_enumset1(X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_15]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_42,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 != esk4_0
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])])).

cnf(c_0_46,negated_conjecture,
    ( esk2_0 = esk4_0
    | r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_48])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:21:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.12/0.38  # and selection function SelectNegativeLiterals.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.038 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t34_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 0.12/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.12/0.38  fof(t77_enumset1, axiom, ![X1, X2]:k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_enumset1)).
% 0.12/0.38  fof(t79_enumset1, axiom, ![X1, X2, X3, X4]:k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_enumset1)).
% 0.12/0.38  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 0.12/0.38  fof(t84_enumset1, axiom, ![X1, X2, X3]:k4_enumset1(X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_enumset1)).
% 0.12/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.12/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4))), inference(assume_negation,[status(cth)],[t34_zfmisc_1])).
% 0.12/0.38  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.12/0.38  fof(c_0_9, plain, ![X15, X16]:k2_enumset1(X15,X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t77_enumset1])).
% 0.12/0.38  fof(c_0_10, plain, ![X17, X18, X19, X20]:k4_enumset1(X17,X17,X17,X18,X19,X20)=k2_enumset1(X17,X18,X19,X20), inference(variable_rename,[status(thm)],[t79_enumset1])).
% 0.12/0.38  fof(c_0_11, negated_conjecture, ((~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0)))|(esk2_0!=esk4_0|esk3_0!=esk5_0))&((esk2_0=esk4_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0))))&(esk3_0=esk5_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.12/0.38  fof(c_0_12, plain, ![X14]:k1_enumset1(X14,X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.12/0.38  fof(c_0_13, plain, ![X21, X22, X23]:k4_enumset1(X21,X21,X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t84_enumset1])).
% 0.12/0.38  cnf(c_0_14, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_15, plain, (k2_enumset1(X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_16, plain, (k4_enumset1(X1,X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0)))|esk2_0!=esk4_0|esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_19, plain, (k4_enumset1(X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (esk3_0=esk5_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (esk2_0=esk4_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k1_tarski(esk4_0),k1_tarski(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_22, plain, ![X24, X25, X26, X27]:(((r2_hidden(X24,X26)|~r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)))&(r2_hidden(X25,X27)|~r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27))))&(~r2_hidden(X24,X26)|~r2_hidden(X25,X27)|r2_hidden(k4_tarski(X24,X25),k2_zfmisc_1(X26,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.12/0.38  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X4,X4,X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (esk4_0!=esk2_0|esk5_0!=esk3_0|~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (esk5_0=esk3_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (esk4_0=esk2_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.12/0.38  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_28, plain, (r2_hidden(X1,k4_enumset1(X2,X2,X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.12/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])).
% 0.12/0.38  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k4_enumset1(X3,X3,X3,X3,X3,X1),X4))|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.38  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_15]), c_0_16])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|~r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.12/0.38  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k4_enumset1(X3,X3,X3,X3,X3,X1),k4_enumset1(X4,X4,X4,X4,X4,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 0.12/0.38  cnf(c_0_35, plain, (r2_hidden(X1,k4_enumset1(X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_32])])).
% 0.12/0.38  cnf(c_0_36, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_37, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.12/0.38  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k4_enumset1(X1,X1,X1,X1,X1,X3),X4))|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 0.12/0.38  cnf(c_0_40, plain, (X1=X4|X1=X3|X2!=k4_enumset1(X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_15]), c_0_16])).
% 0.12/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.12/0.38  cnf(c_0_42, plain, (X1=X2|X1=X3|~r2_hidden(X1,k4_enumset1(X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_0,k4_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_41])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (esk5_0=esk3_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (esk2_0!=esk4_0|~r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])])).
% 0.12/0.38  cnf(c_0_46, negated_conjecture, (esk2_0=esk4_0|r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44])).
% 0.12/0.38  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk3_0),k2_zfmisc_1(k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34])])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk2_0,k4_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.38  cnf(c_0_50, negated_conjecture, (esk2_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_48])])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_49]), c_0_50]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 52
% 0.12/0.38  # Proof object clause steps            : 37
% 0.12/0.38  # Proof object formula steps           : 15
% 0.12/0.38  # Proof object conjectures             : 21
% 0.12/0.38  # Proof object clause conjectures      : 18
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 13
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 11
% 0.12/0.38  # Proof object simplifying inferences  : 46
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 7
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 16
% 0.12/0.38  # Removed in clause preprocessing      : 4
% 0.12/0.38  # Initial clauses in saturation        : 12
% 0.12/0.38  # Processed clauses                    : 69
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 7
% 0.12/0.38  # ...remaining for further processing  : 62
% 0.12/0.38  # Other redundant clauses eliminated   : 15
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 4
% 0.12/0.38  # Backward-rewritten                   : 22
% 0.12/0.38  # Generated clauses                    : 293
% 0.12/0.38  # ...of the previous two non-trivial   : 239
% 0.12/0.38  # Contextual simplify-reflections      : 2
% 0.12/0.38  # Paramodulations                      : 276
% 0.12/0.38  # Factorizations                       : 4
% 0.12/0.38  # Equation resolutions                 : 15
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 21
% 0.12/0.38  #    Positive orientable unit clauses  : 7
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 13
% 0.12/0.38  # Current number of unprocessed clauses: 173
% 0.12/0.38  # ...number of literals in the above   : 651
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 42
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 414
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 253
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.12/0.38  # Unit Clause-clause subsumption calls : 34
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 17
% 0.12/0.38  # BW rewrite match successes           : 6
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 8210
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.043 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.050 s
% 0.12/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
