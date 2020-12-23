%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : ordinal1__t14_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  36 expanded)
%              Number of clauses        :    9 (  16 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   21 (  39 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t14_ordinal1.p',t10_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t14_ordinal1.p',d1_ordinal1)).

fof(t14_ordinal1,conjecture,(
    ! [X1] : X1 != k1_ordinal1(X1) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t14_ordinal1.p',t14_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t14_ordinal1.p',antisymmetry_r2_hidden)).

fof(c_0_4,plain,(
    ! [X12] : r2_hidden(X12,k1_ordinal1(X12)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_5,plain,(
    ! [X8] : k1_ordinal1(X8) = k2_xboole_0(X8,k1_tarski(X8)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] : X1 != k1_ordinal1(X1) ),
    inference(assume_negation,[status(cth)],[t14_ordinal1])).

fof(c_0_7,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,negated_conjecture,(
    esk1_0 = k1_ordinal1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( esk1_0 = k1_ordinal1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(k2_xboole_0(X1,k1_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( esk1_0 = k2_xboole_0(esk1_0,k1_tarski(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
