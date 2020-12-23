%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 776 expanded)
%              Number of clauses        :   59 ( 289 expanded)
%              Number of leaves         :   14 ( 188 expanded)
%              Depth                    :   12
%              Number of atoms          :  391 (6631 expanded)
%              Number of equality atoms :   36 (  36 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_waybel_9)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(dt_l1_waybel_9,axiom,(
    ! [X1] :
      ( l1_waybel_9(X1)
     => ( l1_pre_topc(X1)
        & l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_yellow_6)).

fof(dt_k4_waybel_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( v1_funct_1(k4_waybel_1(X1,X2))
        & v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_yellow_6)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(fc2_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | ~ v1_lattice3(X11)
      | ~ v2_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_16,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X29] :
      ( ( l1_pre_topc(X29)
        | ~ l1_waybel_9(X29) )
      & ( l1_orders_2(X29)
        | ~ l1_waybel_9(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).

cnf(c_0_18,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( l1_orders_2(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l1_waybel_9(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
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

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    | ~ l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X27,X28] :
      ( ( v1_funct_1(k4_waybel_1(X27,X28))
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) )
      & ( v1_funct_2(k4_waybel_1(X27,X28),u1_struct_0(X27),u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) )
      & ( m1_subset_1(k4_waybel_1(X27,X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X27))))
        | v2_struct_0(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).

fof(c_0_26,plain,(
    ! [X30,X31,X32] :
      ( v2_struct_0(X30)
      | ~ l1_orders_2(X30)
      | v2_struct_0(X31)
      | ~ l1_waybel_0(X31,X30)
      | ~ m1_subset_1(X32,u1_struct_0(X30))
      | k6_waybel_9(X30,X30,k4_waybel_1(X30,X32),X31) = k3_waybel_2(X30,X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_waybel_9])])])])).

fof(c_0_27,plain,(
    ! [X22,X23,X24,X25] :
      ( ( X24 != k4_waybel_1(X22,X23)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | k3_funct_2(u1_struct_0(X22),u1_struct_0(X22),X24,X25) = k11_lattice3(X22,X23,X25)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22))))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk1_3(X22,X23,X24),u1_struct_0(X22))
        | X24 = k4_waybel_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22))))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) )
      & ( k3_funct_2(u1_struct_0(X22),u1_struct_0(X22),X24,esk1_3(X22,X23,X24)) != k11_lattice3(X22,X23,esk1_3(X22,X23,X24))
        | X24 = k4_waybel_1(X22,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22))))
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | v2_struct_0(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_waybel_1])])])])])])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v3_yellow_6(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v7_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v8_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

fof(c_0_37,plain,(
    ! [X33,X34,X35] :
      ( ~ v2_pre_topc(X33)
      | ~ v8_pre_topc(X33)
      | ~ v3_orders_2(X33)
      | ~ v4_orders_2(X33)
      | ~ v5_orders_2(X33)
      | ~ v1_lattice3(X33)
      | ~ v2_lattice3(X33)
      | ~ l1_waybel_9(X33)
      | v2_struct_0(X34)
      | ~ v4_orders_2(X34)
      | ~ v7_waybel_0(X34)
      | ~ v3_yellow_6(X34,X33)
      | ~ l1_waybel_0(X34,X33)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X33))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))
      | ~ v5_pre_topc(X35,X33,X33)
      | r2_hidden(k2_yellow_6(u1_struct_0(X33),X33,X35,k11_yellow_6(X33,X34)),k10_yellow_6(X33,k6_waybel_9(X33,X33,X35,X34))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_waybel_9])])])])).

cnf(c_0_38,plain,
    ( m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,plain,
    ( v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( v1_funct_1(k4_waybel_1(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k6_waybel_9(X1,X1,k4_waybel_1(X1,X3),X2) = k3_waybel_2(X1,X3,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_43,plain,(
    ! [X18,X19,X20,X21] :
      ( v1_xboole_0(X18)
      | v2_struct_0(X19)
      | ~ l1_orders_2(X19)
      | ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,X18,u1_struct_0(X19))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,u1_struct_0(X19))))
      | ~ m1_subset_1(X21,X18)
      | k2_yellow_6(X18,X19,X20,X21) = k1_funct_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k2_yellow_6])])])).

fof(c_0_44,plain,(
    ! [X5,X6,X7,X8] :
      ( v1_xboole_0(X5)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X5,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X8,X5)
      | k3_funct_2(X5,X6,X7,X8) = k1_funct_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_45,plain,
    ( k3_funct_2(u1_struct_0(X2),u1_struct_0(X2),X1,X4) = k11_lattice3(X2,X3,X4)
    | v2_struct_0(X2)
    | X1 != k4_waybel_1(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0))
    | ~ l1_pre_topc(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36])).

cnf(c_0_47,plain,
    ( l1_pre_topc(X1)
    | ~ l1_waybel_9(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_48,plain,(
    ! [X12,X13,X14] :
      ( ~ v5_orders_2(X12)
      | ~ v2_lattice3(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | k12_lattice3(X12,X13,X14) = k11_lattice3(X12,X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_49,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( v5_pre_topc(k4_waybel_1(esk2_0,esk4_0),esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v2_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k4_waybel_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24])]),c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(k4_waybel_1(esk2_0,esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_24])]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k4_waybel_1(esk2_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_24])]),c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,X1),esk3_0) = k3_waybel_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_24])]),c_0_35]),c_0_36])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | k2_yellow_6(X1,X2,X3,X4) = k1_funct_1(X3,X4)
    | ~ l1_orders_2(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X3) = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_41]),c_0_40]),c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_21])])).

cnf(c_0_63,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,X1)),k10_yellow_6(esk2_0,k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),X1)))
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,esk2_0)
    | ~ v3_yellow_6(X1,esk2_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_21]),c_0_52]),c_0_33]),c_0_34]),c_0_53]),c_0_54]),c_0_19]),c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_65,negated_conjecture,
    ( k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),esk3_0) = k3_waybel_2(esk2_0,esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),X1) = k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_24]),c_0_55]),c_0_57])]),c_0_36])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1) = k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_55]),c_0_57])])).

cnf(c_0_68,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,X1),k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_24])]),c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( k12_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_62]),c_0_53]),c_0_54]),c_0_24])])).

fof(c_0_70,plain,(
    ! [X17] :
      ( v2_struct_0(X17)
      | ~ l1_orders_2(X17)
      | ~ v1_xboole_0(k2_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_yellow_0])])])).

fof(c_0_71,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | k2_struct_0(X9) = u1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_72,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | l1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_29]),c_0_65]),c_0_30]),c_0_31]),c_0_32])]),c_0_35])).

cnf(c_0_74,negated_conjecture,
    ( k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,negated_conjecture,
    ( k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_39])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)) = k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_hidden(k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_24])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t26_waybel_9, conjecture, ![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(v5_pre_topc(k4_waybel_1(X1,X3),X1,X1)=>r2_hidden(k12_lattice3(X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k3_waybel_2(X1,X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_waybel_9)).
% 0.13/0.38  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.13/0.38  fof(dt_l1_waybel_9, axiom, ![X1]:(l1_waybel_9(X1)=>(l1_pre_topc(X1)&l1_orders_2(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 0.13/0.38  fof(dt_k11_yellow_6, axiom, ![X1, X2]:(((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v8_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_yellow_6)).
% 0.13/0.38  fof(dt_k4_waybel_1, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((v1_funct_1(k4_waybel_1(X1,X2))&v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_1)).
% 0.13/0.38  fof(t18_waybel_9, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k6_waybel_9(X1,X1,k4_waybel_1(X1,X3),X2)=k3_waybel_2(X1,X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_waybel_9)).
% 0.13/0.38  fof(d18_waybel_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))=>(X3=k4_waybel_1(X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),X3,X4)=k11_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_waybel_1)).
% 0.13/0.38  fof(t25_waybel_9, axiom, ![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X1,X1)=>r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_waybel_9)).
% 0.13/0.38  fof(redefinition_k2_yellow_6, axiom, ![X1, X2, X3, X4]:(((((((~(v1_xboole_0(X1))&~(v2_struct_0(X2)))&l1_orders_2(X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2)))))&m1_subset_1(X4,X1))=>k2_yellow_6(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_yellow_6)).
% 0.13/0.38  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.13/0.38  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.13/0.38  fof(fc2_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_yellow_0)).
% 0.13/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:((((((((v2_pre_topc(X1)&v8_pre_topc(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_waybel_9(X1))=>![X2]:(((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&v3_yellow_6(X2,X1))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(v5_pre_topc(k4_waybel_1(X1,X3),X1,X1)=>r2_hidden(k12_lattice3(X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k3_waybel_2(X1,X3,X2)))))))), inference(assume_negation,[status(cth)],[t26_waybel_9])).
% 0.13/0.38  fof(c_0_15, plain, ![X11]:(~l1_orders_2(X11)|(~v1_lattice3(X11)|~v2_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ((((((((v2_pre_topc(esk2_0)&v8_pre_topc(esk2_0))&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&v2_lattice3(esk2_0))&l1_waybel_9(esk2_0))&(((((~v2_struct_0(esk3_0)&v4_orders_2(esk3_0))&v7_waybel_0(esk3_0))&v3_yellow_6(esk3_0,esk2_0))&l1_waybel_0(esk3_0,esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(v5_pre_topc(k4_waybel_1(esk2_0,esk4_0),esk2_0,esk2_0)&~r2_hidden(k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X29]:((l1_pre_topc(X29)|~l1_waybel_9(X29))&(l1_orders_2(X29)|~l1_waybel_9(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_9])])])).
% 0.13/0.38  cnf(c_0_18, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_20, plain, (l1_orders_2(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (l1_waybel_9(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_22, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~v8_pre_topc(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~v4_orders_2(X16)|~v7_waybel_0(X16)|~v3_yellow_6(X16,X15)|~l1_waybel_0(X16,X15)|m1_subset_1(k11_yellow_6(X15,X16),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k11_yellow_6])])])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)|~l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk2_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  fof(c_0_25, plain, ![X27, X28]:(((v1_funct_1(k4_waybel_1(X27,X28))|(v2_struct_0(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,u1_struct_0(X27))))&(v1_funct_2(k4_waybel_1(X27,X28),u1_struct_0(X27),u1_struct_0(X27))|(v2_struct_0(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,u1_struct_0(X27)))))&(m1_subset_1(k4_waybel_1(X27,X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X27))))|(v2_struct_0(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,u1_struct_0(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_1])])])])).
% 0.13/0.38  fof(c_0_26, plain, ![X30, X31, X32]:(v2_struct_0(X30)|~l1_orders_2(X30)|(v2_struct_0(X31)|~l1_waybel_0(X31,X30)|(~m1_subset_1(X32,u1_struct_0(X30))|k6_waybel_9(X30,X30,k4_waybel_1(X30,X32),X31)=k3_waybel_2(X30,X32,X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_waybel_9])])])])).
% 0.13/0.38  fof(c_0_27, plain, ![X22, X23, X24, X25]:((X24!=k4_waybel_1(X22,X23)|(~m1_subset_1(X25,u1_struct_0(X22))|k3_funct_2(u1_struct_0(X22),u1_struct_0(X22),X24,X25)=k11_lattice3(X22,X23,X25))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X22))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22)))))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l1_orders_2(X22)))&((m1_subset_1(esk1_3(X22,X23,X24),u1_struct_0(X22))|X24=k4_waybel_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X22))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22)))))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l1_orders_2(X22)))&(k3_funct_2(u1_struct_0(X22),u1_struct_0(X22),X24,esk1_3(X22,X23,X24))!=k11_lattice3(X22,X23,esk1_3(X22,X23,X24))|X24=k4_waybel_1(X22,X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X22))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X22)))))|~m1_subset_1(X23,u1_struct_0(X22))|(v2_struct_0(X22)|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_waybel_1])])])])])])).
% 0.13/0.38  cnf(c_0_28, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(k11_yellow_6(X1,X2),u1_struct_0(X1))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~l1_pre_topc(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v3_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v3_yellow_6(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (l1_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (v7_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v8_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.13/0.38  fof(c_0_37, plain, ![X33, X34, X35]:(~v2_pre_topc(X33)|~v8_pre_topc(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~v1_lattice3(X33)|~v2_lattice3(X33)|~l1_waybel_9(X33)|(v2_struct_0(X34)|~v4_orders_2(X34)|~v7_waybel_0(X34)|~v3_yellow_6(X34,X33)|~l1_waybel_0(X34,X33)|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X33))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))|(~v5_pre_topc(X35,X33,X33)|r2_hidden(k2_yellow_6(u1_struct_0(X33),X33,X35,k11_yellow_6(X33,X34)),k10_yellow_6(X33,k6_waybel_9(X33,X33,X35,X34))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_waybel_9])])])])).
% 0.13/0.38  cnf(c_0_38, plain, (m1_subset_1(k4_waybel_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_40, plain, (v1_funct_2(k4_waybel_1(X1,X2),u1_struct_0(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_41, plain, (v1_funct_1(k4_waybel_1(X1,X2))|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k6_waybel_9(X1,X1,k4_waybel_1(X1,X3),X2)=k3_waybel_2(X1,X3,X2)|~l1_orders_2(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  fof(c_0_43, plain, ![X18, X19, X20, X21]:(v1_xboole_0(X18)|v2_struct_0(X19)|~l1_orders_2(X19)|~v1_funct_1(X20)|~v1_funct_2(X20,X18,u1_struct_0(X19))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,u1_struct_0(X19))))|~m1_subset_1(X21,X18)|k2_yellow_6(X18,X19,X20,X21)=k1_funct_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k2_yellow_6])])])).
% 0.13/0.38  fof(c_0_44, plain, ![X5, X6, X7, X8]:(v1_xboole_0(X5)|~v1_funct_1(X7)|~v1_funct_2(X7,X5,X6)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|~m1_subset_1(X8,X5)|k3_funct_2(X5,X6,X7,X8)=k1_funct_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.13/0.38  cnf(c_0_45, plain, (k3_funct_2(u1_struct_0(X2),u1_struct_0(X2),X1,X4)=k11_lattice3(X2,X3,X4)|v2_struct_0(X2)|X1!=k4_waybel_1(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0))|~l1_pre_topc(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_47, plain, (l1_pre_topc(X1)|~l1_waybel_9(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_48, plain, ![X12, X13, X14]:(~v5_orders_2(X12)|~v2_lattice3(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,u1_struct_0(X12))|~m1_subset_1(X14,u1_struct_0(X12))|k12_lattice3(X12,X13,X14)=k11_lattice3(X12,X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.13/0.38  cnf(c_0_49, plain, (v2_struct_0(X2)|r2_hidden(k2_yellow_6(u1_struct_0(X1),X1,X3,k11_yellow_6(X1,X2)),k10_yellow_6(X1,k6_waybel_9(X1,X1,X3,X2)))|~v2_pre_topc(X1)|~v8_pre_topc(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v1_lattice3(X1)|~v2_lattice3(X1)|~l1_waybel_9(X1)|~v4_orders_2(X2)|~v7_waybel_0(X2)|~v3_yellow_6(X2,X1)|~l1_waybel_0(X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~v5_pre_topc(X3,X1,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (v5_pre_topc(k4_waybel_1(esk2_0,esk4_0),esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (v2_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (m1_subset_1(k4_waybel_1(esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_24])]), c_0_36])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (v1_funct_2(k4_waybel_1(esk2_0,esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_24])]), c_0_36])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (v1_funct_1(k4_waybel_1(esk2_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_24])]), c_0_36])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,X1),esk3_0)=k3_waybel_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_30]), c_0_24])]), c_0_35]), c_0_36])).
% 0.13/0.38  cnf(c_0_59, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|k2_yellow_6(X1,X2,X3,X4)=k1_funct_1(X3,X4)|~l1_orders_2(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(X2))))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_60, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_61, plain, (k3_funct_2(u1_struct_0(X1),u1_struct_0(X1),k4_waybel_1(X1,X2),X3)=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_41]), c_0_40]), c_0_38])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(k11_yellow_6(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_21])])).
% 0.13/0.38  cnf(c_0_63, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,X1)),k10_yellow_6(esk2_0,k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),X1)))|v2_struct_0(X1)|~l1_waybel_0(X1,esk2_0)|~v3_yellow_6(X1,esk2_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_21]), c_0_52]), c_0_33]), c_0_34]), c_0_53]), c_0_54]), c_0_19]), c_0_55]), c_0_56]), c_0_57])])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (k6_waybel_9(esk2_0,esk2_0,k4_waybel_1(esk2_0,esk4_0),esk3_0)=k3_waybel_2(esk2_0,esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_39])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),X1)=k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1)|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_56]), c_0_24]), c_0_55]), c_0_57])]), c_0_36])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, (k1_funct_1(k4_waybel_1(esk2_0,esk4_0),X1)=k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),X1)|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_56]), c_0_55]), c_0_57])])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,X1),k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_24])]), c_0_36])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (k12_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,X1,k11_yellow_6(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_62]), c_0_53]), c_0_54]), c_0_24])])).
% 0.13/0.38  fof(c_0_70, plain, ![X17]:(v2_struct_0(X17)|~l1_orders_2(X17)|~v1_xboole_0(k2_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_yellow_0])])])).
% 0.13/0.38  fof(c_0_71, plain, ![X9]:(~l1_struct_0(X9)|k2_struct_0(X9)=u1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.38  fof(c_0_72, plain, ![X10]:(~l1_orders_2(X10)|l1_struct_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (r2_hidden(k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_29]), c_0_65]), c_0_30]), c_0_31]), c_0_32])]), c_0_35])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (k2_yellow_6(u1_struct_0(esk2_0),esk2_0,k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_62])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_67, c_0_62])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (k3_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk2_0),k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_68, c_0_39])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (~r2_hidden(k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (k12_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_69, c_0_39])).
% 0.13/0.38  cnf(c_0_79, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.38  cnf(c_0_80, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.13/0.38  cnf(c_0_81, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (r2_hidden(k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (k1_funct_1(k4_waybel_1(esk2_0,esk4_0),k11_yellow_6(esk2_0,esk3_0))=k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (~r2_hidden(k11_lattice3(esk2_0,esk4_0,k11_yellow_6(esk2_0,esk3_0)),k10_yellow_6(esk2_0,k3_waybel_2(esk2_0,esk4_0,esk3_0)))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.38  cnf(c_0_85, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.13/0.38  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_24])]), c_0_36]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 88
% 0.13/0.38  # Proof object clause steps            : 59
% 0.13/0.38  # Proof object formula steps           : 29
% 0.13/0.38  # Proof object conjectures             : 44
% 0.13/0.38  # Proof object clause conjectures      : 41
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 32
% 0.13/0.38  # Proof object initial formulas used   : 14
% 0.13/0.38  # Proof object generating inferences   : 23
% 0.13/0.38  # Proof object simplifying inferences  : 69
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 14
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 34
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 34
% 0.13/0.38  # Processed clauses                    : 124
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 124
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 19
% 0.13/0.38  # Generated clauses                    : 88
% 0.13/0.38  # ...of the previous two non-trivial   : 93
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 87
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 70
% 0.13/0.38  #    Positive orientable unit clauses  : 34
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 33
% 0.13/0.38  # Current number of unprocessed clauses: 37
% 0.13/0.38  # ...number of literals in the above   : 88
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 53
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1281
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 277
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 32
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 42
% 0.13/0.38  # BW rewrite match successes           : 8
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 7315
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.042 s
% 0.13/0.38  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
