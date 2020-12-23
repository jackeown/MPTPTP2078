%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : finset_1__t14_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   10 (  16 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    2 (   4 expanded)
%              Depth                    :    4
%              Number of atoms          :   22 (  40 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_finset_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t14_finset_1.p',t14_finset_1)).

fof(fc9_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t14_finset_1.p',fc9_finset_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_finset_1(X1)
          & v1_finset_1(X2) )
       => v1_finset_1(k2_xboole_0(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t14_finset_1])).

fof(c_0_3,negated_conjecture,
    ( v1_finset_1(esk1_0)
    & v1_finset_1(esk2_0)
    & ~ v1_finset_1(k2_xboole_0(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X8,X9] :
      ( ~ v1_finset_1(X8)
      | ~ v1_finset_1(X9)
      | v1_finset_1(k2_xboole_0(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_finset_1])])).

cnf(c_0_5,negated_conjecture,
    ( ~ v1_finset_1(k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( v1_finset_1(k2_xboole_0(X1,X2))
    | ~ v1_finset_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),c_0_8])]),
    [proof]).
%------------------------------------------------------------------------------
