%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1856+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 101 expanded)
%              Number of clauses        :   18 (  34 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 499 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v2_pre_topc(k1_tex_2(X1,X2))
           => ( v1_tdlat_3(k1_tex_2(X1,X2))
              & v2_tdlat_3(k1_tex_2(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(cc4_tex_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & ~ v2_tdlat_3(X1) )
       => ( ~ v2_struct_0(X1)
          & ~ v7_struct_0(X1)
          & v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tex_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc3_tex_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & ~ v1_tdlat_3(X1) )
       => ( ~ v2_struct_0(X1)
          & ~ v7_struct_0(X1)
          & v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tex_1)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v2_pre_topc(k1_tex_2(X1,X2))
             => ( v1_tdlat_3(k1_tex_2(X1,X2))
                & v2_tdlat_3(k1_tex_2(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_tex_2])).

fof(c_0_7,plain,(
    ! [X5,X6] :
      ( ( ~ v2_struct_0(k1_tex_2(X5,X6))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5)) )
      & ( v1_pre_topc(k1_tex_2(X5,X6))
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5)) )
      & ( m1_pre_topc(k1_tex_2(X5,X6),X5)
        | v2_struct_0(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & v2_pre_topc(k1_tex_2(esk1_0,esk2_0))
    & ( ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))
      | ~ v2_tdlat_3(k1_tex_2(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | v2_tdlat_3(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ v7_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | v2_tdlat_3(X4)
        | ~ l1_pre_topc(X4) )
      & ( v2_pre_topc(X4)
        | v2_struct_0(X4)
        | ~ v2_pre_topc(X4)
        | v2_tdlat_3(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc4_tex_1])])])])).

fof(c_0_10,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_11,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))
    | ~ v2_tdlat_3(k1_tex_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X1)
    | ~ v7_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(k1_tex_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))
    | ~ l1_pre_topc(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13])])).

fof(c_0_22,plain,(
    ! [X3] :
      ( ( ~ v2_struct_0(X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | v1_tdlat_3(X3)
        | ~ l1_pre_topc(X3) )
      & ( ~ v7_struct_0(X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | v1_tdlat_3(X3)
        | ~ l1_pre_topc(X3) )
      & ( v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | v1_tdlat_3(X3)
        | ~ l1_pre_topc(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc3_tex_1])])])])).

cnf(c_0_23,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | v1_tdlat_3(X1)
    | ~ v7_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X9,X10] :
      ( ( ~ v2_struct_0(k1_tex_2(X9,X10))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9)) )
      & ( v7_struct_0(k1_tex_2(X9,X10))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9)) )
      & ( v1_pre_topc(k1_tex_2(X9,X10))
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_26,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17]),c_0_21])])).

cnf(c_0_27,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_12]),c_0_13])]),c_0_14]),
    [proof]).

%------------------------------------------------------------------------------
