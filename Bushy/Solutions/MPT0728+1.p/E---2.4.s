%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t10_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   57 (  57 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_ordinal1,conjecture,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t10_ordinal1.p',t10_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t10_ordinal1.p',d1_ordinal1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t10_ordinal1.p',d3_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t10_ordinal1.p',d1_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(assume_negation,[status(cth)],[t10_ordinal1])).

fof(c_0_5,negated_conjecture,(
    ~ r2_hidden(esk1_0,k1_ordinal1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_6,plain,(
    ! [X10] : k1_ordinal1(X10) = k2_xboole_0(X10,k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X20)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk3_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk3_3(X23,X24,X25),X25)
        | X25 = k2_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk3_3(X23,X24,X25),X24)
        | ~ r2_hidden(esk3_3(X23,X24,X25),X25)
        | X25 = k2_xboole_0(X23,X24) )
      & ( r2_hidden(esk3_3(X23,X24,X25),X25)
        | r2_hidden(esk3_3(X23,X24,X25),X23)
        | r2_hidden(esk3_3(X23,X24,X25),X24)
        | X25 = k2_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_8,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | X13 = X11
        | X12 != k1_tarski(X11) )
      & ( X14 != X11
        | r2_hidden(X14,X12)
        | X12 != k1_tarski(X11) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | esk2_2(X15,X16) != X15
        | X16 = k1_tarski(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | esk2_2(X15,X16) = X15
        | X16 = k1_tarski(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_ordinal1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k2_xboole_0(esk1_0,k1_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_16,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),
    [proof]).
%------------------------------------------------------------------------------
