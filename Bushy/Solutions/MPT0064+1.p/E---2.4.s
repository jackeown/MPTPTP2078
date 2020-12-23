%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : xboole_1__t57_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:29 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :    9 (  12 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    2 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_xboole_1,conjecture,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t57_xboole_1.p',t57_xboole_1)).

fof(antisymmetry_r2_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
     => ~ r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t57_xboole_1.p',antisymmetry_r2_xboole_0)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t57_xboole_1])).

fof(c_0_3,plain,(
    ! [X6,X7] :
      ( ~ r2_xboole_0(X6,X7)
      | ~ r2_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_xboole_0])])])).

fof(c_0_4,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0)
    & r2_xboole_0(esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r2_xboole_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])]),
    [proof]).
%------------------------------------------------------------------------------
