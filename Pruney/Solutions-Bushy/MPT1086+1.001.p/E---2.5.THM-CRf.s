%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1086+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:43 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_finset_1)).

fof(fc9_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_finset_1)).

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
    ! [X3,X4] :
      ( ~ v1_finset_1(X3)
      | ~ v1_finset_1(X4)
      | v1_finset_1(k2_xboole_0(X3,X4)) ) ),
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
