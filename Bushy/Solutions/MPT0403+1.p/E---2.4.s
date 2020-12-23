%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t29_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   28 (  65 expanded)
%              Number of clauses        :   17 (  29 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 208 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_setfam_1,conjecture,(
    ! [X1] : r1_setfam_1(X1,k2_setfam_1(X1,X1)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t29_setfam_1.p',t29_setfam_1)).

fof(d2_setfam_1,axiom,(
    ! [X1,X2] :
      ( r1_setfam_1(X1,X2)
    <=> ! [X3] :
          ~ ( r2_hidden(X3,X1)
            & ! [X4] :
                ~ ( r2_hidden(X4,X2)
                  & r1_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t29_setfam_1.p',d2_setfam_1)).

fof(d4_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_setfam_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k2_xboole_0(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t29_setfam_1.p',d4_setfam_1)).

fof(reflexivity_r1_setfam_1,axiom,(
    ! [X1,X2] : r1_setfam_1(X1,X1) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t29_setfam_1.p',reflexivity_r1_setfam_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t29_setfam_1.p',idempotence_k2_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] : r1_setfam_1(X1,k2_setfam_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t29_setfam_1])).

fof(c_0_6,negated_conjecture,(
    ~ r1_setfam_1(esk1_0,k2_setfam_1(esk1_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X18,X19,X21] :
      ( ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | ~ r2_hidden(X16,X14)
        | ~ r1_setfam_1(X14,X15) )
      & ( r1_tarski(X16,esk2_3(X14,X15,X16))
        | ~ r2_hidden(X16,X14)
        | ~ r1_setfam_1(X14,X15) )
      & ( r2_hidden(esk3_2(X18,X19),X18)
        | r1_setfam_1(X18,X19) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r1_tarski(esk3_2(X18,X19),X21)
        | r1_setfam_1(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_setfam_1])])])])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_setfam_1(esk1_0,k2_setfam_1(esk1_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,plain,(
    ! [X22,X23,X24,X25,X28,X29,X30,X31,X32,X33,X35,X36] :
      ( ( r2_hidden(esk4_4(X22,X23,X24,X25),X22)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_setfam_1(X22,X23) )
      & ( r2_hidden(esk5_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | X24 != k2_setfam_1(X22,X23) )
      & ( X25 = k2_xboole_0(esk4_4(X22,X23,X24,X25),esk5_4(X22,X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_setfam_1(X22,X23) )
      & ( ~ r2_hidden(X29,X22)
        | ~ r2_hidden(X30,X23)
        | X28 != k2_xboole_0(X29,X30)
        | r2_hidden(X28,X24)
        | X24 != k2_setfam_1(X22,X23) )
      & ( ~ r2_hidden(esk6_3(X31,X32,X33),X33)
        | ~ r2_hidden(X35,X31)
        | ~ r2_hidden(X36,X32)
        | esk6_3(X31,X32,X33) != k2_xboole_0(X35,X36)
        | X33 = k2_setfam_1(X31,X32) )
      & ( r2_hidden(esk7_3(X31,X32,X33),X31)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_setfam_1(X31,X32) )
      & ( r2_hidden(esk8_3(X31,X32,X33),X32)
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_setfam_1(X31,X32) )
      & ( esk6_3(X31,X32,X33) = k2_xboole_0(esk7_3(X31,X32,X33),esk8_3(X31,X32,X33))
        | r2_hidden(esk6_3(X31,X32,X33),X33)
        | X33 = k2_setfam_1(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_setfam_1])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_setfam_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_13,plain,(
    ! [X42] : r1_setfam_1(X42,X42) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r1_setfam_1])])).

cnf(c_0_14,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k2_xboole_0(X1,X3)
    | X6 != k2_setfam_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_3(esk1_0,X1,esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0))),X1)
    | ~ r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( r1_setfam_1(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X2)
    | ~ r1_setfam_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(k2_xboole_0(X1,X2),k2_setfam_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk2_3(esk1_0,esk1_0,esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0))),esk1_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X41] : k2_xboole_0(X41,X41) = X41 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0)),esk2_3(esk1_0,X1,esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0))))
    | ~ r1_setfam_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k2_xboole_0(X1,esk2_3(esk1_0,esk1_0,esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0)))),k2_setfam_1(X2,esk1_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r1_setfam_1(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(esk3_2(X3,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0)),esk2_3(esk1_0,esk1_0,esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_3(esk1_0,esk1_0,esk3_2(esk1_0,k2_setfam_1(esk1_0,esk1_0))),k2_setfam_1(esk1_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_8]),
    [proof]).
%------------------------------------------------------------------------------
