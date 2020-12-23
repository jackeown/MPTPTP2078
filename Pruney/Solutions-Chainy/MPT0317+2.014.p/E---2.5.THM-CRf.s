%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:46 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 136 expanded)
%              Number of clauses        :   25 (  62 expanded)
%              Number of leaves         :    4 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 375 expanded)
%              Number of equality atoms :   21 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t129_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
    <=> ( r2_hidden(X1,X3)
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(t76_enumset1,axiom,(
    ! [X1] : k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))
      <=> ( r2_hidden(X1,X3)
          & X2 = X4 ) ) ),
    inference(assume_negation,[status(cth)],[t129_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13] :
      ( ( X10 = X12
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(k1_tarski(X12),X13)) )
      & ( r2_hidden(X11,X13)
        | ~ r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(k1_tarski(X12),X13)) )
      & ( X10 != X12
        | ~ r2_hidden(X11,X13)
        | r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(k1_tarski(X12),X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

fof(c_0_6,plain,(
    ! [X5] : k1_enumset1(X5,X5,X5) = k1_tarski(X5) ),
    inference(variable_rename,[status(thm)],[t76_enumset1])).

fof(c_0_7,negated_conjecture,
    ( ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))
      | ~ r2_hidden(esk1_0,esk3_0)
      | esk2_0 != esk4_0 )
    & ( r2_hidden(esk1_0,esk3_0)
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))) )
    & ( esk2_0 = esk4_0
      | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))
    | X1 != X2
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k1_enumset1(X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X6,X7,X8,X9] :
      ( ( r2_hidden(X6,X8)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( r2_hidden(X7,X9)
        | ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) )
      & ( ~ r2_hidden(X6,X8)
        | ~ r2_hidden(X7,X9)
        | r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),X4))
    | X1 != X2
    | ~ r2_hidden(X3,X4) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_enumset1(X1,X1,X1),X3))
    | ~ r2_hidden(X2,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = esk4_0
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_0),k2_zfmisc_1(k1_enumset1(X1,X1,X1),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))
    | ~ r2_hidden(esk1_0,esk3_0)
    | esk2_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( esk4_0 = esk2_0
    | r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_9])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 != esk2_0
    | ~ r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_0),k2_zfmisc_1(X2,esk3_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( esk2_0 = esk4_0
    | r2_hidden(esk2_0,k1_enumset1(esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),X4)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_enumset1(X2,X2,X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( esk2_0 != esk4_0
    | ~ r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_16])])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,X1),k2_zfmisc_1(esk3_0,k1_enumset1(X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.21/0.40  # and selection function SelectNewComplexAHP.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.050 s
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t129_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 0.21/0.40  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.21/0.40  fof(t76_enumset1, axiom, ![X1]:k1_enumset1(X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 0.21/0.40  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.21/0.40  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_tarski(X4)))<=>(r2_hidden(X1,X3)&X2=X4))), inference(assume_negation,[status(cth)],[t129_zfmisc_1])).
% 0.21/0.40  fof(c_0_5, plain, ![X10, X11, X12, X13]:(((X10=X12|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(k1_tarski(X12),X13)))&(r2_hidden(X11,X13)|~r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(k1_tarski(X12),X13))))&(X10!=X12|~r2_hidden(X11,X13)|r2_hidden(k4_tarski(X10,X11),k2_zfmisc_1(k1_tarski(X12),X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.21/0.40  fof(c_0_6, plain, ![X5]:k1_enumset1(X5,X5,X5)=k1_tarski(X5), inference(variable_rename,[status(thm)],[t76_enumset1])).
% 0.21/0.40  fof(c_0_7, negated_conjecture, ((~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))|(~r2_hidden(esk1_0,esk3_0)|esk2_0!=esk4_0))&((r2_hidden(esk1_0,esk3_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))&(esk2_0=esk4_0|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.21/0.40  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))|X1!=X2|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  cnf(c_0_9, plain, (k1_enumset1(X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  fof(c_0_10, plain, ![X6, X7, X8, X9]:(((r2_hidden(X6,X8)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))&(r2_hidden(X7,X9)|~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9))))&(~r2_hidden(X6,X8)|~r2_hidden(X7,X9)|r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(X8,X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.21/0.40  cnf(c_0_11, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.40  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),X4))|X1!=X2|~r2_hidden(X3,X4)), inference(rw,[status(thm)],[c_0_8, c_0_9])).
% 0.21/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_14, negated_conjecture, (r2_hidden(esk1_0,esk3_0)|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[c_0_11, c_0_9])).
% 0.21/0.40  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_enumset1(X1,X1,X1),X3))|~r2_hidden(X2,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.40  cnf(c_0_17, negated_conjecture, (esk2_0=esk4_0|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_0),k2_zfmisc_1(k1_enumset1(X1,X1,X1),esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.40  cnf(c_0_19, negated_conjecture, (~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))|~r2_hidden(esk1_0,esk3_0)|esk2_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.40  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_21, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (esk4_0=esk2_0|r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[c_0_17, c_0_9])).
% 0.21/0.40  cnf(c_0_23, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.40  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,k1_enumset1(X1,X1,X1))), inference(spm,[status(thm)],[c_0_13, c_0_18])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (esk4_0!=esk2_0|~r2_hidden(esk1_0,esk3_0)|~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))), inference(rw,[status(thm)],[c_0_19, c_0_9])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_0),k2_zfmisc_1(X2,esk3_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.21/0.40  cnf(c_0_27, negated_conjecture, (esk2_0=esk4_0|r2_hidden(esk2_0,k1_enumset1(esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.40  cnf(c_0_28, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_enumset1(X2,X2,X2),X4))), inference(rw,[status(thm)],[c_0_23, c_0_9])).
% 0.21/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,k1_enumset1(X2,X2,X2)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_20, c_0_24])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (esk2_0!=esk4_0|~r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,k1_enumset1(esk4_0,esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_16])])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (esk2_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk1_0,X1),k2_zfmisc_1(esk3_0,k1_enumset1(X1,X1,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_16])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31]), c_0_32])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 34
% 0.21/0.40  # Proof object clause steps            : 25
% 0.21/0.40  # Proof object formula steps           : 9
% 0.21/0.40  # Proof object conjectures             : 19
% 0.21/0.40  # Proof object clause conjectures      : 16
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 9
% 0.21/0.40  # Proof object initial formulas used   : 4
% 0.21/0.40  # Proof object generating inferences   : 8
% 0.21/0.40  # Proof object simplifying inferences  : 13
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 4
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 10
% 0.21/0.40  # Removed in clause preprocessing      : 1
% 0.21/0.40  # Initial clauses in saturation        : 9
% 0.21/0.40  # Processed clauses                    : 25
% 0.21/0.40  # ...of these trivial                  : 2
% 0.21/0.40  # ...subsumed                          : 1
% 0.21/0.40  # ...remaining for further processing  : 22
% 0.21/0.40  # Other redundant clauses eliminated   : 1
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 6
% 0.21/0.40  # Generated clauses                    : 62
% 0.21/0.40  # ...of the previous two non-trivial   : 55
% 0.21/0.40  # Contextual simplify-reflections      : 1
% 0.21/0.40  # Paramodulations                      : 61
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 1
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 15
% 0.21/0.40  #    Positive orientable unit clauses  : 7
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 0
% 0.21/0.40  #    Non-unit-clauses                  : 8
% 0.21/0.40  # Current number of unprocessed clauses: 38
% 0.21/0.40  # ...number of literals in the above   : 60
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 7
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 27
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 24
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 2
% 0.21/0.40  # Unit Clause-clause subsumption calls : 23
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 4
% 0.21/0.40  # BW rewrite match successes           : 2
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 1539
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.052 s
% 0.21/0.40  # System time              : 0.004 s
% 0.21/0.40  # Total time               : 0.057 s
% 0.21/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
