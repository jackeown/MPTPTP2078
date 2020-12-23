%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   19 (  32 expanded)
%              Number of clauses        :   10 (  11 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 ( 101 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_finset_1(u1_struct_0(X1))
       => v1_compts_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_compts_1)).

fof(fc9_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v8_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_finset_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_struct_0)).

fof(cc3_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( v8_struct_0(X1)
          & v2_pre_topc(X1) )
       => ( v2_pre_topc(X1)
          & v1_compts_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_compts_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ( v1_finset_1(u1_struct_0(X1))
         => v1_compts_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t27_compts_1])).

fof(c_0_5,plain,(
    ! [X4] :
      ( v8_struct_0(X4)
      | ~ l1_struct_0(X4)
      | ~ v1_finset_1(u1_struct_0(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_struct_0])])])).

fof(c_0_6,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & v1_finset_1(u1_struct_0(esk1_0))
    & ~ v1_compts_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X2] :
      ( ( v2_pre_topc(X2)
        | ~ v8_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2) )
      & ( v1_compts_1(X2)
        | ~ v8_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_compts_1])])])).

cnf(c_0_8,plain,
    ( v8_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_finset_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_finset_1(u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_compts_1(X1)
    | ~ v8_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v8_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_compts_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_15,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(X3)
      | l1_struct_0(X3) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_16,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13])]),
    [proof]).

%------------------------------------------------------------------------------
