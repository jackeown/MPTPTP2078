%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1615+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:27 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   18 (  24 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   43 (  67 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k3_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

fof(t13_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(t5_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t23_yellow_1])).

fof(c_0_5,plain,(
    ! [X3] :
      ( v1_xboole_0(X3)
      | ~ r2_hidden(k1_xboole_0,X3)
      | k3_yellow_0(k2_yellow_1(X3)) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).

fof(c_0_6,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & k3_yellow_0(k2_yellow_1(u1_pre_topc(esk1_0))) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( v1_xboole_0(X1)
    | k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(u1_pre_topc(esk1_0))) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_12,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),
    [proof]).

%------------------------------------------------------------------------------
