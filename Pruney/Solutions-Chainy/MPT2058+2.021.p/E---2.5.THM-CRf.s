%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 (1052 expanded)
%              Number of clauses        :   56 ( 400 expanded)
%              Number of leaves         :   10 ( 268 expanded)
%              Depth                    :   16
%              Number of atoms          :  446 (5856 expanded)
%              Number of equality atoms :    9 ( 322 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | v1_xboole_0(X21)
      | ~ v1_subset_1(X21,u1_struct_0(k3_yellow_1(k2_struct_0(X20))))
      | ~ v2_waybel_0(X21,k3_yellow_1(k2_struct_0(X20)))
      | ~ v13_waybel_0(X21,k3_yellow_1(k2_struct_0(X20)))
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X20)))))
      | X21 = k2_yellow19(X20,k3_yellow19(X20,k2_struct_0(X20),X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_12,plain,(
    ! [X7] : k3_yellow_1(X7) = k3_lattice3(k1_lattice3(X7)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))
    & v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
      | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0) )
    & ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
      | r1_waybel_7(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r3_waybel_9(X17,X18,X19)
        | r1_waybel_7(X17,k2_yellow19(X17,X18),X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X18)
        | ~ v4_orders_2(X18)
        | ~ v7_waybel_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) )
      & ( ~ r1_waybel_7(X17,k2_yellow19(X17,X18),X19)
        | r3_waybel_9(X17,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | v2_struct_0(X18)
        | ~ v4_orders_2(X18)
        | ~ v7_waybel_0(X18)
        | ~ l1_waybel_0(X18,X17)
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( ( ~ v2_struct_0(k3_yellow19(X14,X15,X16))
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v1_xboole_0(X16)
        | ~ v1_subset_1(X16,u1_struct_0(k3_yellow_1(X15)))
        | ~ v2_waybel_0(X16,k3_yellow_1(X15))
        | ~ v13_waybel_0(X16,k3_yellow_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X15)))) )
      & ( v6_waybel_0(k3_yellow19(X14,X15,X16),X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v1_xboole_0(X16)
        | ~ v1_subset_1(X16,u1_struct_0(k3_yellow_1(X15)))
        | ~ v2_waybel_0(X16,k3_yellow_1(X15))
        | ~ v13_waybel_0(X16,k3_yellow_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X15)))) )
      & ( v7_waybel_0(k3_yellow19(X14,X15,X16))
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v1_xboole_0(X16)
        | ~ v1_subset_1(X16,u1_struct_0(k3_yellow_1(X15)))
        | ~ v2_waybel_0(X16,k3_yellow_1(X15))
        | ~ v13_waybel_0(X16,k3_yellow_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X15)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_22,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v2_struct_0(k3_yellow19(X11,X12,X13))
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,k3_yellow_1(X12))
        | ~ v13_waybel_0(X13,k3_yellow_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12)))) )
      & ( v3_orders_2(k3_yellow19(X11,X12,X13))
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,k3_yellow_1(X12))
        | ~ v13_waybel_0(X13,k3_yellow_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12)))) )
      & ( v4_orders_2(k3_yellow19(X11,X12,X13))
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,k3_yellow_1(X12))
        | ~ v13_waybel_0(X13,k3_yellow_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12)))) )
      & ( v6_waybel_0(k3_yellow19(X11,X12,X13),X11)
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | v1_xboole_0(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | v1_xboole_0(X13)
        | ~ v2_waybel_0(X13,k3_yellow_1(X12))
        | ~ v13_waybel_0(X13,k3_yellow_1(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_34,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | l1_struct_0(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_37,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_struct_0(k3_yellow19(X8,X9,X10))
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) )
      & ( v6_waybel_0(k3_yellow19(X8,X9,X10),X8)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) )
      & ( l1_waybel_0(k3_yellow19(X8,X9,X10),X8)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_waybel_7(esk1_0,k2_yellow19(esk1_0,X1),esk3_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk1_0,X1,esk3_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v7_waybel_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_16]),c_0_16]),c_0_16]),c_0_16])).

fof(c_0_43,plain,(
    ! [X4] :
      ( ~ l1_struct_0(X4)
      | m1_subset_1(k2_struct_0(X4),k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_45,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_47])]),c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_49]),c_0_47])]),c_0_27])).

cnf(c_0_56,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_47])])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_49]),c_0_47])]),c_0_27])).

cnf(c_0_62,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_64,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,X1)
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_54]),c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_47])]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_49]),c_0_47])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_70,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_24])])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_68])).

fof(c_0_72,plain,(
    ! [X6] :
      ( v2_struct_0(X6)
      | ~ l1_struct_0(X6)
      | ~ v1_xboole_0(k2_struct_0(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_71]),c_0_47])]),c_0_27])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_49]),c_0_47])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_47])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:21:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.032 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 0.19/0.38  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.19/0.38  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.19/0.38  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 0.19/0.38  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.19/0.38  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.19/0.38  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.19/0.38  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.19/0.38  fof(c_0_11, plain, ![X20, X21]:(v2_struct_0(X20)|~l1_struct_0(X20)|(v1_xboole_0(X21)|~v1_subset_1(X21,u1_struct_0(k3_yellow_1(k2_struct_0(X20))))|~v2_waybel_0(X21,k3_yellow_1(k2_struct_0(X20)))|~v13_waybel_0(X21,k3_yellow_1(k2_struct_0(X20)))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X20)))))|X21=k2_yellow19(X20,k3_yellow19(X20,k2_struct_0(X20),X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.19/0.38  fof(c_0_12, plain, ![X7]:k3_yellow_1(X7)=k3_lattice3(k1_lattice3(X7)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((((~v1_xboole_0(esk2_0)&v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))&v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&((~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0))&(r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X17, X18, X19]:((~r3_waybel_9(X17,X18,X19)|r1_waybel_7(X17,k2_yellow19(X17,X18),X19)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X18)|~v4_orders_2(X18)|~v7_waybel_0(X18)|~l1_waybel_0(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))&(~r1_waybel_7(X17,k2_yellow19(X17,X18),X19)|r3_waybel_9(X17,X18,X19)|~m1_subset_1(X19,u1_struct_0(X17))|(v2_struct_0(X18)|~v4_orders_2(X18)|~v7_waybel_0(X18)|~l1_waybel_0(X18,X17))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.19/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_21, plain, ![X14, X15, X16]:(((~v2_struct_0(k3_yellow19(X14,X15,X16))|(v2_struct_0(X14)|~l1_struct_0(X14)|v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|v1_xboole_0(X16)|~v1_subset_1(X16,u1_struct_0(k3_yellow_1(X15)))|~v2_waybel_0(X16,k3_yellow_1(X15))|~v13_waybel_0(X16,k3_yellow_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X15))))))&(v6_waybel_0(k3_yellow19(X14,X15,X16),X14)|(v2_struct_0(X14)|~l1_struct_0(X14)|v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|v1_xboole_0(X16)|~v1_subset_1(X16,u1_struct_0(k3_yellow_1(X15)))|~v2_waybel_0(X16,k3_yellow_1(X15))|~v13_waybel_0(X16,k3_yellow_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X15)))))))&(v7_waybel_0(k3_yellow19(X14,X15,X16))|(v2_struct_0(X14)|~l1_struct_0(X14)|v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|v1_xboole_0(X16)|~v1_subset_1(X16,u1_struct_0(k3_yellow_1(X15)))|~v2_waybel_0(X16,k3_yellow_1(X15))|~v13_waybel_0(X16,k3_yellow_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X15))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.19/0.38  fof(c_0_22, plain, ![X11, X12, X13]:((((~v2_struct_0(k3_yellow19(X11,X12,X13))|(v2_struct_0(X11)|~l1_struct_0(X11)|v1_xboole_0(X12)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|v1_xboole_0(X13)|~v2_waybel_0(X13,k3_yellow_1(X12))|~v13_waybel_0(X13,k3_yellow_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12))))))&(v3_orders_2(k3_yellow19(X11,X12,X13))|(v2_struct_0(X11)|~l1_struct_0(X11)|v1_xboole_0(X12)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|v1_xboole_0(X13)|~v2_waybel_0(X13,k3_yellow_1(X12))|~v13_waybel_0(X13,k3_yellow_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12)))))))&(v4_orders_2(k3_yellow19(X11,X12,X13))|(v2_struct_0(X11)|~l1_struct_0(X11)|v1_xboole_0(X12)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|v1_xboole_0(X13)|~v2_waybel_0(X13,k3_yellow_1(X12))|~v13_waybel_0(X13,k3_yellow_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12)))))))&(v6_waybel_0(k3_yellow19(X11,X12,X13),X11)|(v2_struct_0(X11)|~l1_struct_0(X11)|v1_xboole_0(X12)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|v1_xboole_0(X13)|~v2_waybel_0(X13,k3_yellow_1(X12))|~v13_waybel_0(X13,k3_yellow_1(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X12))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.19/0.38  cnf(c_0_23, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_28, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_16]), c_0_16]), c_0_16])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))))), inference(rw,[status(thm)],[c_0_17, c_0_16])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))), inference(rw,[status(thm)],[c_0_18, c_0_16])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_19, c_0_16])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_20, c_0_16])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_34, plain, ![X5]:(~l1_pre_topc(X5)|l1_struct_0(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_35, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_36, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_37, plain, ![X8, X9, X10]:(((~v2_struct_0(k3_yellow19(X8,X9,X10))|(v2_struct_0(X8)|~l1_struct_0(X8)|v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|v1_xboole_0(X10)|~v2_waybel_0(X10,k3_yellow_1(X9))|~v13_waybel_0(X10,k3_yellow_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9))))))&(v6_waybel_0(k3_yellow19(X8,X9,X10),X8)|(v2_struct_0(X8)|~l1_struct_0(X8)|v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|v1_xboole_0(X10)|~v2_waybel_0(X10,k3_yellow_1(X9))|~v13_waybel_0(X10,k3_yellow_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))))))&(l1_waybel_0(k3_yellow19(X8,X9,X10),X8)|(v2_struct_0(X8)|~l1_struct_0(X8)|v1_xboole_0(X9)|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|v1_xboole_0(X10)|~v2_waybel_0(X10,k3_yellow_1(X9))|~v13_waybel_0(X10,k3_yellow_1(X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r1_waybel_7(esk1_0,k2_yellow19(esk1_0,X1),esk3_0)|v2_struct_0(X1)|~r3_waybel_9(esk1_0,X1,esk3_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))=esk2_0|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32])]), c_0_33]), c_0_27])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_42, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_16]), c_0_16]), c_0_16]), c_0_16])).
% 0.19/0.38  fof(c_0_43, plain, ![X4]:(~l1_struct_0(X4)|m1_subset_1(k2_struct_0(X4),k1_zfmisc_1(u1_struct_0(X4)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.19/0.38  cnf(c_0_44, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_16]), c_0_16]), c_0_16])).
% 0.19/0.38  cnf(c_0_45, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_41, c_0_26])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_29]), c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.19/0.38  cnf(c_0_49, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.19/0.38  cnf(c_0_51, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_16]), c_0_16]), c_0_16])).
% 0.19/0.38  cnf(c_0_52, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_47])]), c_0_27])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_49]), c_0_47])]), c_0_27])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.19/0.38  cnf(c_0_57, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_47])])).
% 0.19/0.38  cnf(c_0_59, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_16]), c_0_16]), c_0_16])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|v1_xboole_0(k2_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_49]), c_0_47])]), c_0_27])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,X1)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_25]), c_0_26])]), c_0_27])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_29]), c_0_31]), c_0_32])]), c_0_33])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,X1)|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_54]), c_0_55])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_47])]), c_0_27])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_65, c_0_61])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_49]), c_0_47])])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_24])])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_68])).
% 0.19/0.38  fof(c_0_72, plain, ![X6]:(v2_struct_0(X6)|~l1_struct_0(X6)|~v1_xboole_0(k2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_71]), c_0_47])]), c_0_27])).
% 0.19/0.38  cnf(c_0_74, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_49]), c_0_47])])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_47])]), c_0_27]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 77
% 0.19/0.38  # Proof object clause steps            : 56
% 0.19/0.38  # Proof object formula steps           : 21
% 0.19/0.38  # Proof object conjectures             : 43
% 0.19/0.38  # Proof object clause conjectures      : 40
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 22
% 0.19/0.38  # Proof object initial formulas used   : 10
% 0.19/0.38  # Proof object generating inferences   : 23
% 0.19/0.38  # Proof object simplifying inferences  : 84
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 10
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 28
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 27
% 0.19/0.38  # Processed clauses                    : 70
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 8
% 0.19/0.38  # ...remaining for further processing  : 62
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 9
% 0.19/0.38  # Backward-rewritten                   : 15
% 0.19/0.38  # Generated clauses                    : 47
% 0.19/0.38  # ...of the previous two non-trivial   : 47
% 0.19/0.38  # Contextual simplify-reflections      : 5
% 0.19/0.38  # Paramodulations                      : 45
% 0.19/0.38  # Factorizations                       : 2
% 0.19/0.38  # Equation resolutions                 : 0
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
% 0.19/0.38  # Current number of processed clauses  : 38
% 0.19/0.38  #    Positive orientable unit clauses  : 10
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 26
% 0.19/0.38  # Current number of unprocessed clauses: 1
% 0.19/0.38  # ...number of literals in the above   : 6
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 25
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 684
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 73
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 21
% 0.19/0.38  # Unit Clause-clause subsumption calls : 28
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 2
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6174
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.039 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.042 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
