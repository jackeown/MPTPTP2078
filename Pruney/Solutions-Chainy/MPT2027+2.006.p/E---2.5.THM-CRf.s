%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 773 expanded)
%              Number of clauses        :   59 ( 288 expanded)
%              Number of leaves         :   13 ( 187 expanded)
%              Depth                    :   14
%              Number of atoms          :  384 (6623 expanded)
%              Number of equality atoms :   33 (  33 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   25 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_waybel_9,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_waybel_9(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v3_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( v5_pre_topc(k4_waybel_1(X1,X3),X1,X1)
               => r2_hidden(k12_lattice3(X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k3_waybel_2(X1,X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_waybel_9)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(dt_k11_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & v3_yellow_6(X2,X1)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(dt_k4_waybel_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( v1_funct_1(k4_waybel_1(X1,X2))
        & v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_1)).

fof(t18_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k6_waybel_9(X1,X1,k4_waybel_1(X1,X3),X2) = k3_waybel_2(X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_9)).

fof(d18_waybel_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
             => ( X3 = k4_waybel_1(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),X3,X4) = k11_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_1)).

fof(t25_waybel_9,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & v8_pre_topc(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_waybel_9(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & v3_yellow_6(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X1,X1)
               => r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_9)).

fof(redefinition_k2_yellow_6,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v2_struct_0(X2)
        & l1_orders_2(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
        & m1_subset_1(X4,X1) )
     => k2_yellow_6(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & v8_pre_topc(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_waybel_9(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & v3_yellow_6(X2,X1)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( v5_pre_topc(k4_waybel_1(X1,X3),X1,X1)
                 => r2_hidden(k12_lattice3(X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k3_waybel_2(X1,X3,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_waybel_9])).

fof(c_0_14,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ v2_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & v8_pre_topc(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & v1_lattice3(esk2_0)
    & v2_lattice3(esk2_0)
    & l1_waybel_9(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v4_orders_2(esk3_0)
    & v7_waybel_0(esk3_0)
    & v3_yellow_6(esk3_0,esk2_0)
    & l1_waybel_0(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & v5_pre_topc(k4_waybel_1(esk2_0,esk4_0),esk2_0,esk2_0)
    & ~ r2_hidden(k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X28] :
      ( ( l1_pre_topc(X28)
        | ~ l1_waybel_9(X28) )
      & ( l1_orders_2(X28)
        | ~ l1_waybel_9(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_17,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_waybel_9(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ v8_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ v4_orders_2(X16)
      | ~ v7_waybel_0(X16)
      | ~ v3_yellow_6(X16,X15)
      | ~ l1_waybel_0(X16,X15)
      | m1_subset_1(k11_yellow_6(X15,X16),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k11_yellow_6])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ l1_orders_2(esk2_0)
    | ~ v2_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_24,plain,(
    ! [X26,X27] :
      ( ( v1_funct_1(k4_waybel_1(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) )
      & ( v1_funct_2(k4_waybel_1(X26,X27),u1_struct_0(X26),u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) )
      & ( m1_subset_1(k4_waybel_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X26))))
        | v2_struct_0(X26)
        | ~ l1_orders_2(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).

fof(c_0_25,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ l1_orders_2(X29)
      | v2_struct_0(X30)
      | ~ l1_waybel_0(X30,X29)
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | k6_waybel_9(X29,X29,k4_waybel_1(X29,X31),X30) = k3_waybel_2(X29,X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_waybel_9])])])])).

fof(c_0_26,plain,(
    ! [X21,X22,X23,X24] :
      ( ( X23 != k4_waybel_1(X21,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | k3_funct_2(u1_struct_0(X21),u1_struct_0(X21),X23,X24) = k11_lattice3(X21,X22,X24)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X21))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X21))))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_orders_2(X21) )
      & ( m1_subset_1(esk1_3(X21,X22,X23),u1_struct_0(X21))
        | X23 = k4_waybel_1(X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X21))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X21))))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_orders_2(X21) )
      & ( k3_funct_2(u1_struct_0(X21),u1_struct_0(X21),X23,esk1_3(X21,X22,X23)) != k11_lattice3(X21,X22,esk1_3(X21,X22,X23))
        | X23 = k4_waybel_1(X21,X22)
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X21))
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X21))))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ l1_orders_2(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_waybel_1])])])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v3_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v3_yellow_6(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( v8_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

fof(c_0_36,plain,(
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ v8_pre_topc(X32)
      | ~ v3_orders_2(X32)
      | ~ v4_orders_2(X32)
      | ~ v5_orders_2(X32)
      | ~ v1_lattice3(X32)
      | ~ v2_lattice3(X32)
      | ~ l1_waybel_9(X32)
      | v2_struct_0(X33)
      | ~ v4_orders_2(X33)
      | ~ v7_waybel_0(X33)
      | ~ v3_yellow_6(X33,X32)
      | ~ l1_waybel_0(X33,X32)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X32))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X32))))
      | ~ v5_pre_topc(X34,X32,X32)
      | r2_hidden(k2_yellow_6(u1_struct_0(X32),X32,X34,k11_yellow_6(X32,X33)),k10_yellow_6(X32,k6_waybel_9(X32,X32,X34,X33))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_waybel_9])])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,plain,
    ( v1_funct_1(k4_waybel_1(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X3),X2) = k3_waybel_2(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_42,plain,(
    ! [X17,X18,X19,X20] :
      ( v1_xboole_0(X17)
      | v2_struct_0(X18)
      | ~ l1_orders_2(X18)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,X17,u1_struct_0(X18))
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,u1_struct_0(X18))))
      | ~ m1_subset_1(X20,X17)
      | k2_yellow_6(X17,X18,X19,X20) = k1_funct_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k2_yellow_6])])])).

fof(c_0_43,plain,(
    ! [X5,X6,X7,X8] :
      ( v1_xboole_0(X5)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X5,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X8,X5)
      | k3_funct_2(X5,X6,X7,X8) = k1_funct_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_44,plain,
    ( k3_funct_2(u1_struct_0(X2),u1_struct_0(X2),X1,X4) = k11_lattice3(X2,X3,X4)
    | v2_struct_0(X2)
    | X1 != k4_waybel_1(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0))
    | ~ l1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_47,plain,(
    ! [X12,X13,X14] :
      ( ~ v5_orders_2(X12)
      | ~ v2_lattice3(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | k12_lattice3(X12,X13,X14) = k11_lattice3(X12,X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X2)
    | r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X3,X2)))
    | ~ v2_pre_topc(X1)
    | ~ v8_pre_topc(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_waybel_9(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ v3_yellow_6(X2,X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ v5_pre_topc(X3,X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,esk4_0),esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k4_waybel_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23])]),c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(k4_waybel_1(esk2_0,esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_23])]),c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(k4_waybel_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_23])]),c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,X1),esk3_0) = k3_waybel_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_23])]),c_0_34]),c_0_35])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | k2_yellow_6(X1,X2,X3,X4) = k1_funct_1(X3,X4)
    | ~ l1_orders_2(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X3) = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_40]),c_0_39]),c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_20])])).

cnf(c_0_62,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,X1)),k10_yellow_6(esk2_0,k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),X1)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk2_0)
    | ~ v3_yellow_6(X1,esk2_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_20]),c_0_52]),c_0_32]),c_0_33]),c_0_53]),c_0_18]),c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),esk3_0) = k3_waybel_2(esk2_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_65,negated_conjecture,
    ( k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),X1) = k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_55]),c_0_23]),c_0_54]),c_0_56])]),c_0_35])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1) = k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_54]),c_0_56])])).

cnf(c_0_67,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,X1),k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_23])]),c_0_35])).

cnf(c_0_68,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_53]),c_0_18]),c_0_23])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_28]),c_0_64]),c_0_29]),c_0_30]),c_0_31])]),c_0_34])).

cnf(c_0_70,negated_conjecture,
    ( k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_38])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_38])).

fof(c_0_75,plain,(
    ! [X10] :
      ( v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | ~ v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

fof(c_0_81,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_82,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_35])).

cnf(c_0_83,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( ~ l1_pre_topc(esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_46]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t26_waybel_9, conjecture, ![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(v5_pre_topc(k4_waybel_1(X1,X3),X1,X1)=>r2_hidden(k12_lattice3(X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k3_waybel_2(X1,X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_waybel_9)).
% 0.19/0.38  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.19/0.38  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.19/0.38  fof(dt_k11_yellow_6, axiom, ![X1, X2]:(((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_yellow_6)).
% 0.19/0.38  fof(dt_k4_waybel_1, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((v1_funct_1(k4_waybel_1(X1,X2))&v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 0.19/0.38  fof(t18_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k6_waybel_9(X1,X1,k4_waybel_1(X1,X3),X2)=k3_waybel_2(X1,X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_waybel_9)).
% 0.19/0.38  fof(d18_waybel_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))=>(X3=k4_waybel_1(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),X3,X4)=k11_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_waybel_1)).
% 0.19/0.38  fof(t25_waybel_9, axiom, ![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X1,X1)=>r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_waybel_9)).
% 0.19/0.38  fof(redefinition_k2_yellow_6, axiom, ![X1, X2, X3, X4]:(((((((~(v1_xboole_0(X1))&~(v2_struct_0(X2)))&l1_orders_2(X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2)))))&m1_subset_1(X4,X1))=>k2_yellow_6(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_yellow_6)).
% 0.19/0.38  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.19/0.38  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.19/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(v5_pre_topc(k4_waybel_1(X1,X3),X1,X1)=>r2_hidden(k12_lattice3(X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k3_waybel_2(X1,X3,X2)))))))), inference(assume_negation,[status(cth)],[t26_waybel_9])).
% 0.19/0.38  fof(c_0_14, plain, ![X11]:(~l1_orders_2(X11)|(~v2_lattice3(X11)|~v2_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, ((((((((v2_pre_topc(esk2_0)&v8_pre_topc(esk2_0))&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&v2_lattice3(esk2_0))&l1_waybel_9(esk2_0))&(((((~v2_struct_0(esk3_0)&v4_orders_2(esk3_0))&v7_waybel_0(esk3_0))&v3_yellow_6(esk3_0,esk2_0))&l1_waybel_0(esk3_0,esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(v5_pre_topc(k4_waybel_1(esk2_0,esk4_0),esk2_0,esk2_0)&~r2_hidden(k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X28]:((l1_pre_topc(X28)|~l1_waybel_9(X28))&(l1_orders_2(X28)|~l1_waybel_9(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.19/0.38  cnf(c_0_17, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (v2_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_19, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (l1_waybel_9(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_21, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~v8_pre_topc(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~v3_yellow_6(X16,X15)|~l1_waybel_0(X16,X15)|m1_subset_1(k11_yellow_6(X15,X16),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k11_yellow_6])])])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (~l1_orders_2(esk2_0)|~v2_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.38  fof(c_0_24, plain, ![X26, X27]:(((v1_funct_1(k4_waybel_1(X26,X27))|(v2_struct_0(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,u1_struct_0(X26))))&(v1_funct_2(k4_waybel_1(X26,X27),u1_struct_0(X26),u1_struct_0(X26))|(v2_struct_0(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,u1_struct_0(X26)))))&(m1_subset_1(k4_waybel_1(X26,X27),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X26))))|(v2_struct_0(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,u1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).
% 0.19/0.38  fof(c_0_25, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~l1_orders_2(X29)|(v2_struct_0(X30)|~l1_waybel_0(X30,X29)|(~m1_subset_1(X31,u1_struct_0(X29))|k6_waybel_9(X29,X29,k4_waybel_1(X29,X31),X30)=k3_waybel_2(X29,X31,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_waybel_9])])])])).
% 0.19/0.38  fof(c_0_26, plain, ![X21, X22, X23, X24]:((X23!=k4_waybel_1(X21,X22)|(~m1_subset_1(X24,u1_struct_0(X21))|k3_funct_2(u1_struct_0(X21),u1_struct_0(X21),X23,X24)=k11_lattice3(X21,X22,X24))|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X21))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X21)))))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l1_orders_2(X21)))&((m1_subset_1(esk1_3(X21,X22,X23),u1_struct_0(X21))|X23=k4_waybel_1(X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X21))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X21)))))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l1_orders_2(X21)))&(k3_funct_2(u1_struct_0(X21),u1_struct_0(X21),X23,esk1_3(X21,X22,X23))!=k11_lattice3(X21,X22,esk1_3(X21,X22,X23))|X23=k4_waybel_1(X21,X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X21))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X21)))))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~l1_orders_2(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_waybel_1])])])])])])).
% 0.19/0.38  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v3_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (v3_yellow_6(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (l1_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (v7_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v8_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.19/0.38  fof(c_0_36, plain, ![X32, X33, X34]:(~v2_pre_topc(X32)|~v8_pre_topc(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~v2_lattice3(X32)|~l1_waybel_9(X32)|(v2_struct_0(X33)|~v4_orders_2(X33)|~v7_waybel_0(X33)|~v3_yellow_6(X33,X32)|~l1_waybel_0(X33,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X32))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X32))))|(~v5_pre_topc(X34,X32,X32)|r2_hidden(k2_yellow_6(u1_struct_0(X32),X32,X34,k11_yellow_6(X32,X33)),k10_yellow_6(X32,k6_waybel_9(X32,X32,X34,X33))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_waybel_9])])])])).
% 0.19/0.38  cnf(c_0_37, plain, (m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_39, plain, (v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_40, plain, (v1_funct_1(k4_waybel_1(X1,X2))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k6_waybel_9(X1,X1,k4_waybel_1(X1,X3),X2)=k3_waybel_2(X1,X3,X2)|~l1_orders_2(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  fof(c_0_42, plain, ![X17, X18, X19, X20]:(v1_xboole_0(X17)|v2_struct_0(X18)|~l1_orders_2(X18)|~v1_funct_1(X19)|~v1_funct_2(X19,X17,u1_struct_0(X18))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,u1_struct_0(X18))))|~m1_subset_1(X20,X17)|k2_yellow_6(X17,X18,X19,X20)=k1_funct_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k2_yellow_6])])])).
% 0.19/0.38  fof(c_0_43, plain, ![X5, X6, X7, X8]:(v1_xboole_0(X5)|~v1_funct_1(X7)|~v1_funct_2(X7,X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|~m1_subset_1(X8,X5)|k3_funct_2(X5,X6,X7,X8)=k1_funct_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.19/0.38  cnf(c_0_44, plain, (k3_funct_2(u1_struct_0(X2),u1_struct_0(X2),X1,X4)=k11_lattice3(X2,X3,X4)|v2_struct_0(X2)|X1!=k4_waybel_1(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0))|~l1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33])]), c_0_34]), c_0_35])).
% 0.19/0.38  cnf(c_0_46, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_47, plain, ![X12, X13, X14]:(~v5_orders_2(X12)|~v2_lattice3(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|k12_lattice3(X12,X13,X14)=k11_lattice3(X12,X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.19/0.38  cnf(c_0_48, plain, (v2_struct_0(X2)|r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X3,X2)))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_waybel_9(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v3_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~v5_pre_topc(X3,X1,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,esk4_0),esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (m1_subset_1(k4_waybel_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23])]), c_0_35])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (v1_funct_2(k4_waybel_1(esk2_0,esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_23])]), c_0_35])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (v1_funct_1(k4_waybel_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_23])]), c_0_35])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,X1),esk3_0)=k3_waybel_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_23])]), c_0_34]), c_0_35])).
% 0.19/0.38  cnf(c_0_58, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|k2_yellow_6(X1,X2,X3,X4)=k1_funct_1(X3,X4)|~l1_orders_2(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_59, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_60, plain, (k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X3)=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_44]), c_0_40]), c_0_39]), c_0_37])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_20])])).
% 0.19/0.38  cnf(c_0_62, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,X1)),k10_yellow_6(esk2_0,k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),X1)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk2_0)|~v3_yellow_6(X1,esk2_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_20]), c_0_52]), c_0_32]), c_0_33]), c_0_53]), c_0_18]), c_0_54]), c_0_55]), c_0_56])])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),esk3_0)=k3_waybel_2(esk2_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),X1)=k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1)|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_55]), c_0_23]), c_0_54]), c_0_56])]), c_0_35])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1)=k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),X1)|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_55]), c_0_54]), c_0_56])])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,X1),k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_23])]), c_0_35])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (k12_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_53]), c_0_18]), c_0_23])])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_28]), c_0_64]), c_0_29]), c_0_30]), c_0_31])]), c_0_34])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_65, c_0_61])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_61])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_67, c_0_38])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (~r2_hidden(k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_38])).
% 0.19/0.38  fof(c_0_75, plain, ![X10]:(v2_struct_0(X10)|~l1_struct_0(X10)|~v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (r2_hidden(k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (~r2_hidden(k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.38  cnf(c_0_79, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.19/0.38  fof(c_0_81, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_35])).
% 0.19/0.38  cnf(c_0_83, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (~l1_pre_topc(esk2_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_46]), c_0_20])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 86
% 0.19/0.38  # Proof object clause steps            : 59
% 0.19/0.38  # Proof object formula steps           : 27
% 0.19/0.38  # Proof object conjectures             : 46
% 0.19/0.38  # Proof object clause conjectures      : 43
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 31
% 0.19/0.38  # Proof object initial formulas used   : 13
% 0.19/0.38  # Proof object generating inferences   : 24
% 0.19/0.38  # Proof object simplifying inferences  : 68
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 13
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 33
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 33
% 0.19/0.38  # Processed clauses                    : 134
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 134
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 20
% 0.19/0.38  # Generated clauses                    : 95
% 0.19/0.38  # ...of the previous two non-trivial   : 100
% 0.19/0.38  # Contextual simplify-reflections      : 3
% 0.19/0.38  # Paramodulations                      : 94
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 80
% 0.19/0.38  #    Positive orientable unit clauses  : 34
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 41
% 0.19/0.38  # Current number of unprocessed clauses: 32
% 0.19/0.38  # ...number of literals in the above   : 102
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 53
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1523
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 537
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.38  # Unit Clause-clause subsumption calls : 131
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 42
% 0.19/0.38  # BW rewrite match successes           : 8
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 7858
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.039 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
