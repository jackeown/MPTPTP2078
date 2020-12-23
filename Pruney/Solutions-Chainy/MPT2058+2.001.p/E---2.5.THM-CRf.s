%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:58 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  112 (1751 expanded)
%              Number of clauses        :   79 ( 760 expanded)
%              Number of leaves         :   16 ( 443 expanded)
%              Depth                    :   19
%              Number of atoms          :  593 (7733 expanded)
%              Number of equality atoms :   29 ( 952 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tops_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(t17_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
              <=> r1_waybel_7(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

fof(t15_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
            & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
         => X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t27_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(t12_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r3_waybel_9(X1,X2,X3)
              <=> r1_waybel_7(X1,k2_yellow19(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k3_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1)
        & l1_waybel_0(k3_yellow19(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(fc5_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1)
        & v7_waybel_0(k3_yellow19(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

fof(fc4_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & ~ v1_xboole_0(X3)
        & v2_waybel_0(X3,k3_yellow_1(X2))
        & v13_waybel_0(X3,k3_yellow_1(X2))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) )
     => ( ~ v2_struct_0(k3_yellow19(X1,X2,X3))
        & v3_orders_2(k3_yellow19(X1,X2,X3))
        & v4_orders_2(k3_yellow19(X1,X2,X3))
        & v6_waybel_0(k3_yellow19(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(c_0_16,plain,(
    ! [X16,X17] :
      ( ( ~ v1_tops_1(X17,X16)
        | k2_pre_topc(X16,X17) = u1_struct_0(X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( k2_pre_topc(X16,X17) != u1_struct_0(X16)
        | v1_tops_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

fof(c_0_17,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | m1_subset_1(k2_struct_0(X8),k1_zfmisc_1(u1_struct_0(X8))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ( ~ v1_tops_1(X13,X12)
        | k2_pre_topc(X12,X13) = k2_struct_0(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( k2_pre_topc(X12,X13) != k2_struct_0(X12)
        | v1_tops_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
              & v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
                <=> r1_waybel_7(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_yellow19])).

cnf(c_0_20,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | v1_xboole_0(X31)
      | ~ v1_subset_1(X31,u1_struct_0(k3_yellow_1(k2_struct_0(X30))))
      | ~ v2_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))
      | ~ v13_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X30)))))
      | X31 = k2_yellow19(X30,k3_yellow19(X30,k2_struct_0(X30),X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_24,plain,(
    ! [X15] : k3_yellow_1(X15) = k3_lattice3(k1_lattice3(X15)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))
    & v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))
    & v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)
      | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0) )
    & ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)
      | r1_waybel_7(esk2_0,esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

cnf(c_0_26,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | ~ v1_tops_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( v1_tops_1(k2_struct_0(X1),X1)
    | k2_pre_topc(X1,k2_struct_0(X1)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_22,c_0_21])).

fof(c_0_28,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | k2_pre_topc(X14,k2_struct_0(X14)) = k2_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | k2_pre_topc(X1,k2_struct_0(X1)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r3_waybel_9(X27,X28,X29)
        | r1_waybel_7(X27,k2_yellow19(X27,X28),X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_waybel_7(X27,k2_yellow19(X27,X28),X29)
        | r3_waybel_9(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_38,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_45,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_46,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(X9)
      | l1_struct_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_47,plain,
    ( r3_waybel_9(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_7(X1,k2_yellow19(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( k2_yellow19(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)) = esk3_0
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42])]),c_0_43]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_51,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_struct_0(k3_yellow19(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( v6_waybel_0(k3_yellow19(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( l1_waybel_0(k3_yellow19(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_52,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_36,c_0_45])).

cnf(c_0_53,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( r1_waybel_7(X1,k2_yellow19(X1,X2),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),X1)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_58,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_52,c_0_53])).

fof(c_0_60,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_61,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,X1)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),X1)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54,c_0_48]),c_0_49]),c_0_50])]),c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)
    | r1_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39,c_0_59]),c_0_50])])).

cnf(c_0_67,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_59]),c_0_50])])).

cnf(c_0_68,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42,c_0_59]),c_0_50])])).

cnf(c_0_69,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_71,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v2_struct_0(k3_yellow19(X24,X25,X26))
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( v6_waybel_0(k3_yellow19(X24,X25,X26),X24)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) )
      & ( v7_waybel_0(k3_yellow19(X24,X25,X26))
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24)
        | v1_xboole_0(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v1_xboole_0(X26)
        | ~ v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))
        | ~ v2_waybel_0(X26,k3_yellow_1(X25))
        | ~ v13_waybel_0(X26,k3_yellow_1(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

cnf(c_0_72,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_57])])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64,c_0_59]),c_0_50])])).

cnf(c_0_74,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_68])]),c_0_44])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,plain,
    ( v7_waybel_0(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_59]),c_0_50])])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73,c_0_74]),c_0_75])]),c_0_43])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_30]),c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_80,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_59]),c_0_50])])).

fof(c_0_81,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v2_struct_0(k3_yellow19(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) )
      & ( v3_orders_2(k3_yellow19(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) )
      & ( v4_orders_2(k3_yellow19(X21,X22,X23))
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) )
      & ( v6_waybel_0(k3_yellow19(X21,X22,X23),X21)
        | v2_struct_0(X21)
        | ~ l1_struct_0(X21)
        | v1_xboole_0(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v1_xboole_0(X23)
        | ~ v2_waybel_0(X23,k3_yellow_1(X22))
        | ~ v13_waybel_0(X23,k3_yellow_1(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_82,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_74]),c_0_75])]),c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78,c_0_59]),c_0_50])])).

cnf(c_0_84,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79,c_0_66]),c_0_80]),c_0_67]),c_0_68])]),c_0_44])).

cnf(c_0_85,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_59]),c_0_50])])).

cnf(c_0_87,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_84]),c_0_75])]),c_0_43])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_84]),c_0_75])]),c_0_43])).

cnf(c_0_90,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_91,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_87,c_0_59]),c_0_50])])).

cnf(c_0_92,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88,c_0_66]),c_0_67]),c_0_68])]),c_0_44])).

cnf(c_0_93,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89,c_0_59]),c_0_50])])).

cnf(c_0_94,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_30]),c_0_30]),c_0_30])).

cnf(c_0_95,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91,c_0_92]),c_0_75])]),c_0_43])).

cnf(c_0_96,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_93,c_0_92]),c_0_75])]),c_0_43])).

fof(c_0_97,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_xboole_0(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_98,plain,(
    ! [X10] :
      ( ( m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v1_xboole_0(esk1_1(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v4_pre_topc(esk1_1(X10),X10)
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

cnf(c_0_99,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94,c_0_66]),c_0_67]),c_0_68])]),c_0_44])).

cnf(c_0_100,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_95,c_0_59]),c_0_50])])).

cnf(c_0_101,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96,c_0_59]),c_0_50])])).

cnf(c_0_102,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_103,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99,c_0_100]),c_0_75])]),c_0_43])).

cnf(c_0_105,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99,c_0_101]),c_0_75])]),c_0_43])).

cnf(c_0_106,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk1_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_107,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(esk1_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_xboole_0(esk1_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_106]),c_0_49]),c_0_50])])).

cnf(c_0_110,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107,c_0_108]),c_0_49]),c_0_50])]),c_0_43]),c_0_109])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110,c_0_53]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.13/0.39  # and selection function NoSelection.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 0.13/0.39  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.13/0.39  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 0.13/0.39  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 0.13/0.39  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.13/0.39  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.13/0.39  fof(t27_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_1)).
% 0.13/0.39  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.13/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.39  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.13/0.39  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.13/0.39  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.13/0.39  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.13/0.39  fof(c_0_16, plain, ![X16, X17]:((~v1_tops_1(X17,X16)|k2_pre_topc(X16,X17)=u1_struct_0(X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(k2_pre_topc(X16,X17)!=u1_struct_0(X16)|v1_tops_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.13/0.39  fof(c_0_17, plain, ![X8]:(~l1_struct_0(X8)|m1_subset_1(k2_struct_0(X8),k1_zfmisc_1(u1_struct_0(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.13/0.39  fof(c_0_18, plain, ![X12, X13]:((~v1_tops_1(X13,X12)|k2_pre_topc(X12,X13)=k2_struct_0(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(k2_pre_topc(X12,X13)!=k2_struct_0(X12)|v1_tops_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.13/0.39  fof(c_0_19, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.13/0.39  cnf(c_0_20, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_21, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_22, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  fof(c_0_23, plain, ![X30, X31]:(v2_struct_0(X30)|~l1_struct_0(X30)|(v1_xboole_0(X31)|~v1_subset_1(X31,u1_struct_0(k3_yellow_1(k2_struct_0(X30))))|~v2_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))|~v13_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X30)))))|X31=k2_yellow19(X30,k3_yellow19(X30,k2_struct_0(X30),X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.13/0.39  fof(c_0_24, plain, ![X15]:k3_yellow_1(X15)=k3_lattice3(k1_lattice3(X15)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.13/0.39  fof(c_0_25, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((((~v1_xboole_0(esk3_0)&v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))&v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))))&v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))))&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|~r1_waybel_7(esk2_0,esk3_0,esk4_0))&(r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|r1_waybel_7(esk2_0,esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.13/0.39  cnf(c_0_26, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|~v1_tops_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.39  cnf(c_0_27, plain, (v1_tops_1(k2_struct_0(X1),X1)|k2_pre_topc(X1,k2_struct_0(X1))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_22, c_0_21])).
% 0.13/0.39  fof(c_0_28, plain, ![X14]:(~l1_pre_topc(X14)|k2_pre_topc(X14,k2_struct_0(X14))=k2_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_tops_1])])).
% 0.13/0.39  cnf(c_0_29, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_30, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_35, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|k2_pre_topc(X1,k2_struct_0(X1))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_36, plain, (k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.39  fof(c_0_37, plain, ![X27, X28, X29]:((~r3_waybel_9(X27,X28,X29)|r1_waybel_7(X27,k2_yellow19(X27,X28),X29)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~r1_waybel_7(X27,k2_yellow19(X27,X28),X29)|r3_waybel_9(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.13/0.39  cnf(c_0_38, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))))), inference(rw,[status(thm)],[c_0_31, c_0_30])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))))), inference(rw,[status(thm)],[c_0_32, c_0_30])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_33, c_0_30])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_34, c_0_30])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_45, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.39  fof(c_0_46, plain, ![X9]:(~l1_pre_topc(X9)|l1_struct_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  cnf(c_0_47, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (k2_yellow19(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))=esk3_0|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42])]), c_0_43]), c_0_44])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  fof(c_0_51, plain, ![X18, X19, X20]:(((~v2_struct_0(k3_yellow19(X18,X19,X20))|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))&(v6_waybel_0(k3_yellow19(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))))))&(l1_waybel_0(k3_yellow19(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.13/0.39  cnf(c_0_52, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_36, c_0_45])).
% 0.13/0.39  cnf(c_0_53, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_54, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|~r1_waybel_7(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),X1)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~r1_waybel_7(esk2_0,esk3_0,X1)|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)|~l1_struct_0(esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])]), c_0_43])).
% 0.13/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_58, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_59, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_52, c_0_53])).
% 0.13/0.39  fof(c_0_60, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.39  fof(c_0_61, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,X1)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),X1)|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)|~l1_struct_0(esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54, c_0_48]), c_0_49]), c_0_50])]), c_0_43])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|r1_waybel_7(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_64, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.13/0.39  cnf(c_0_65, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_69, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.39  cnf(c_0_70, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.39  fof(c_0_71, plain, ![X24, X25, X26]:(((~v2_struct_0(k3_yellow19(X24,X25,X26))|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))&(v6_waybel_0(k3_yellow19(X24,X25,X26),X24)|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))))))&(v7_waybel_0(k3_yellow19(X24,X25,X26))|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_57])])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0),X1)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_68])]), c_0_44])).
% 0.13/0.39  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.39  cnf(c_0_76, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73, c_0_74]), c_0_75])]), c_0_43])).
% 0.13/0.39  cnf(c_0_79, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_30]), c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_59]), c_0_50])])).
% 0.13/0.39  fof(c_0_81, plain, ![X21, X22, X23]:((((~v2_struct_0(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22))))))&(v3_orders_2(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))))))&(v4_orders_2(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))))))&(v6_waybel_0(k3_yellow19(X21,X22,X23),X21)|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_74]), c_0_75])]), c_0_43])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79, c_0_66]), c_0_80]), c_0_67]), c_0_68])]), c_0_44])).
% 0.13/0.39  cnf(c_0_85, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_84]), c_0_75])]), c_0_43])).
% 0.13/0.39  cnf(c_0_88, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.39  cnf(c_0_89, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_84]), c_0_75])]), c_0_43])).
% 0.13/0.39  cnf(c_0_90, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_91, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_87, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_92, negated_conjecture, (v4_orders_2(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88, c_0_66]), c_0_67]), c_0_68])]), c_0_44])).
% 0.13/0.39  cnf(c_0_93, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_94, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_30]), c_0_30]), c_0_30])).
% 0.13/0.39  cnf(c_0_95, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91, c_0_92]), c_0_75])]), c_0_43])).
% 0.13/0.39  cnf(c_0_96, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_93, c_0_92]), c_0_75])]), c_0_43])).
% 0.13/0.39  fof(c_0_97, plain, ![X6, X7]:(~v1_xboole_0(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.13/0.39  fof(c_0_98, plain, ![X10]:(((m1_subset_1(esk1_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~v1_xboole_0(esk1_1(X10))|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10))))&(v4_pre_topc(esk1_1(X10),X10)|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.13/0.39  cnf(c_0_99, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk2_0))|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94, c_0_66]), c_0_67]), c_0_68])]), c_0_44])).
% 0.13/0.39  cnf(c_0_100, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_95, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_101, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_96, c_0_59]), c_0_50])])).
% 0.13/0.39  cnf(c_0_102, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.13/0.39  cnf(c_0_103, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.13/0.39  cnf(c_0_104, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99, c_0_100]), c_0_75])]), c_0_43])).
% 0.13/0.39  cnf(c_0_105, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99, c_0_101]), c_0_75])]), c_0_43])).
% 0.13/0.39  cnf(c_0_106, plain, (v2_struct_0(X1)|~v1_xboole_0(esk1_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.13/0.39  cnf(c_0_107, plain, (v2_struct_0(X1)|v1_xboole_0(esk1_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_102, c_0_103])).
% 0.13/0.39  cnf(c_0_108, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_104, c_0_105])).
% 0.13/0.39  cnf(c_0_109, negated_conjecture, (~v1_xboole_0(esk1_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_106]), c_0_49]), c_0_50])])).
% 0.13/0.39  cnf(c_0_110, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107, c_0_108]), c_0_49]), c_0_50])]), c_0_43]), c_0_109])).
% 0.13/0.39  cnf(c_0_111, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110, c_0_53]), c_0_50])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 112
% 0.13/0.39  # Proof object clause steps            : 79
% 0.13/0.39  # Proof object formula steps           : 33
% 0.13/0.39  # Proof object conjectures             : 51
% 0.13/0.39  # Proof object clause conjectures      : 48
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 29
% 0.13/0.39  # Proof object initial formulas used   : 16
% 0.13/0.39  # Proof object generating inferences   : 40
% 0.13/0.39  # Proof object simplifying inferences  : 115
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 16
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 38
% 0.13/0.39  # Removed in clause preprocessing      : 2
% 0.13/0.39  # Initial clauses in saturation        : 36
% 0.13/0.39  # Processed clauses                    : 210
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 46
% 0.13/0.39  # ...remaining for further processing  : 162
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 25
% 0.13/0.39  # Backward-rewritten                   : 0
% 0.13/0.39  # Generated clauses                    : 271
% 0.13/0.39  # ...of the previous two non-trivial   : 242
% 0.13/0.39  # Contextual simplify-reflections      : 0
% 0.13/0.39  # Paramodulations                      : 271
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 137
% 0.13/0.39  #    Positive orientable unit clauses  : 12
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 6
% 0.13/0.39  #    Non-unit-clauses                  : 119
% 0.13/0.39  # Current number of unprocessed clauses: 55
% 0.13/0.39  # ...number of literals in the above   : 443
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 27
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 740
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 163
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 70
% 0.13/0.39  # Unit Clause-clause subsumption calls : 92
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 4
% 0.13/0.39  # BW rewrite match successes           : 0
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 8910
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.043 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.047 s
% 0.13/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
