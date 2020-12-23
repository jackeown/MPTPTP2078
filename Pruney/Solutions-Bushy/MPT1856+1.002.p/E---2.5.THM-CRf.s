%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1856+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:54 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 101 expanded)
%              Number of clauses        :   18 (  34 expanded)
%              Number of leaves         :    5 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  132 ( 511 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   20 (   2 average)
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

fof(cc1_tex_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( ~ v2_struct_0(X1)
          & v7_struct_0(X1)
          & v2_pre_topc(X1) )
       => ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(fc2_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v7_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v2_pre_topc(k1_tex_2(X1,X2))
             => ( v1_tdlat_3(k1_tex_2(X1,X2))
                & v2_tdlat_3(k1_tex_2(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_tex_2])).

fof(c_0_6,plain,(
    ! [X4,X5] :
      ( ( ~ v2_struct_0(k1_tex_2(X4,X5))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,u1_struct_0(X4)) )
      & ( v1_pre_topc(k1_tex_2(X4,X5))
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,u1_struct_0(X4)) )
      & ( m1_pre_topc(k1_tex_2(X4,X5),X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & v2_pre_topc(k1_tex_2(esk1_0,esk2_0))
    & ( ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))
      | ~ v2_tdlat_3(k1_tex_2(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X3] :
      ( ( ~ v2_struct_0(X3)
        | v2_struct_0(X3)
        | ~ v7_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3) )
      & ( v2_pre_topc(X3)
        | v2_struct_0(X3)
        | ~ v7_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3) )
      & ( v1_tdlat_3(X3)
        | v2_struct_0(X3)
        | ~ v7_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3) )
      & ( v2_tdlat_3(X3)
        | v2_struct_0(X3)
        | ~ v7_struct_0(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_tex_1])])])])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | l1_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_10,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))
    | ~ v2_tdlat_3(k1_tex_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v2_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(k1_tex_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ l1_pre_topc(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12])])).

cnf(c_0_21,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_22,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_23,plain,(
    ! [X8,X9] :
      ( ( ~ v2_struct_0(k1_tex_2(X8,X9))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) )
      & ( v7_struct_0(k1_tex_2(X8,X9))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) )
      & ( v1_pre_topc(k1_tex_2(X8,X9))
        | v2_struct_0(X8)
        | ~ l1_pre_topc(X8)
        | ~ m1_subset_1(X9,u1_struct_0(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_tex_2])])])])).

cnf(c_0_24,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | ~ v7_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16]),c_0_20])])).

cnf(c_0_25,plain,
    ( v7_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_11]),c_0_12])]),c_0_13]),
    [proof]).

%------------------------------------------------------------------------------
