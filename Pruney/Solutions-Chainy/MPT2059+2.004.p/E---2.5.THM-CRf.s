%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:02 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  102 (1075 expanded)
%              Number of clauses        :   73 ( 422 expanded)
%              Number of leaves         :   14 ( 274 expanded)
%              Depth                    :   18
%              Number of atoms          :  548 (5432 expanded)
%              Number of equality atoms :   15 ( 374 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_yellow19,conjecture,(
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
             => ( r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))
              <=> r2_waybel_7(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow19)).

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

fof(t13_yellow19,axiom,(
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
             => ( r2_hidden(X3,k10_yellow_6(X1,X2))
              <=> r2_waybel_7(X1,k2_yellow19(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow19)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(c_0_14,negated_conjecture,(
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
               => ( r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))
                <=> r2_waybel_7(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_yellow19])).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X17] : k3_yellow_1(X17) = k3_lattice3(k1_lattice3(X17)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    & v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ( ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
      | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0) )
    & ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
      | r2_waybel_7(esk3_0,esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r2_hidden(X29,k10_yellow_6(X27,X28))
        | r2_waybel_7(X27,k2_yellow19(X27,X28),X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r2_waybel_7(X27,k2_yellow19(X27,X28),X29)
        | r2_hidden(X29,k10_yellow_6(X27,X28))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v4_orders_2(X28)
        | ~ v7_waybel_0(X28)
        | ~ l1_waybel_0(X28,X27)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).

cnf(c_0_25,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k2_struct_0(X13) = u1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_33,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | l1_struct_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_34,plain,
    ( r2_hidden(X3,k10_yellow_6(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_7(X1,k2_yellow19(X1,X2),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)) = esk4_0
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_38,plain,(
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

cnf(c_0_39,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_waybel_7(X2,k2_yellow19(X2,X3),X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k10_yellow_6(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | r2_hidden(X1,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
    | ~ r2_waybel_7(esk3_0,esk4_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])]),c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

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
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_47,plain,(
    ! [X9] : m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_48,plain,(
    ! [X8] : k2_subset_1(X8) = X8 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_49,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,X1)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_35]),c_0_36]),c_0_37])]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))
    | r2_waybel_7(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26,c_0_46]),c_0_37])])).

cnf(c_0_54,negated_conjecture,
    ( v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28,c_0_46]),c_0_37])])).

cnf(c_0_55,negated_conjecture,
    ( v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_29,c_0_46]),c_0_37])])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_58,plain,(
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

cnf(c_0_59,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_49,c_0_50]),c_0_44])])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0),esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_46]),c_0_37])])).

cnf(c_0_61,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])]),c_0_31])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0),esk3_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59,c_0_46]),c_0_37])])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60,c_0_61]),c_0_62])]),c_0_30])).

cnf(c_0_66,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_19]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_67,negated_conjecture,
    ( v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27,c_0_46]),c_0_37])])).

fof(c_0_68,plain,(
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

cnf(c_0_69,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64,c_0_61]),c_0_62])]),c_0_30])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ v7_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65,c_0_46]),c_0_37])])).

cnf(c_0_71,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_53]),c_0_67]),c_0_54]),c_0_55])]),c_0_31])).

cnf(c_0_72,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_46]),c_0_37])])).

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_71]),c_0_62])]),c_0_30])).

cnf(c_0_75,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_76,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73,c_0_71]),c_0_62])]),c_0_30])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ v4_orders_2(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74,c_0_46]),c_0_37])])).

cnf(c_0_79,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_53]),c_0_54]),c_0_55])]),c_0_31])).

cnf(c_0_80,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_46]),c_0_37])])).

fof(c_0_81,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_82,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78,c_0_79]),c_0_62])]),c_0_30])).

cnf(c_0_85,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80,c_0_79]),c_0_62])]),c_0_30])).

cnf(c_0_86,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_88,plain,(
    ! [X15] :
      ( ( m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ v1_xboole_0(esk2_1(X15))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( v4_pre_topc(esk2_1(X15),X15)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_53]),c_0_54]),c_0_55])]),c_0_31])).

cnf(c_0_90,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84,c_0_46]),c_0_37])])).

cnf(c_0_91,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85,c_0_46]),c_0_37])])).

cnf(c_0_92,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89,c_0_90]),c_0_62])]),c_0_30])).

cnf(c_0_95,negated_conjecture,
    ( r2_waybel_7(esk3_0,esk4_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89,c_0_91]),c_0_62])]),c_0_30])).

cnf(c_0_96,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk2_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_97,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(esk2_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(pm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_xboole_0(esk2_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_96]),c_0_36]),c_0_37])])).

cnf(c_0_100,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97,c_0_98]),c_0_36]),c_0_37])]),c_0_30]),c_0_99])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100,c_0_40]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:38:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.12/0.37  # and selection function NoSelection.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.029 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t18_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow19)).
% 0.12/0.37  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.12/0.37  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.12/0.37  fof(t13_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))<=>r2_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow19)).
% 0.12/0.37  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.12/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.37  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.12/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.12/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.12/0.37  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.12/0.37  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.12/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.12/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.37  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t18_yellow19])).
% 0.12/0.37  fof(c_0_15, plain, ![X30, X31]:(v2_struct_0(X30)|~l1_struct_0(X30)|(v1_xboole_0(X31)|~v1_subset_1(X31,u1_struct_0(k3_yellow_1(k2_struct_0(X30))))|~v2_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))|~v13_waybel_0(X31,k3_yellow_1(k2_struct_0(X30)))|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X30)))))|X31=k2_yellow19(X30,k3_yellow19(X30,k2_struct_0(X30),X31)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.12/0.37  fof(c_0_16, plain, ![X17]:k3_yellow_1(X17)=k3_lattice3(k1_lattice3(X17)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.12/0.37  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((((~v1_xboole_0(esk4_0)&v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))&v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0))))&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&((~r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|~r2_waybel_7(esk3_0,esk4_0,esk5_0))&(r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|r2_waybel_7(esk3_0,esk4_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.12/0.37  cnf(c_0_18, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v13_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (v2_waybel_0(esk4_0,k3_yellow_1(k2_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_24, plain, ![X27, X28, X29]:((~r2_hidden(X29,k10_yellow_6(X27,X28))|r2_waybel_7(X27,k2_yellow19(X27,X28),X29)|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~r2_waybel_7(X27,k2_yellow19(X27,X28),X29)|r2_hidden(X29,k10_yellow_6(X27,X28))|~m1_subset_1(X29,u1_struct_0(X27))|(v2_struct_0(X28)|~v4_orders_2(X28)|~v7_waybel_0(X28)|~l1_waybel_0(X28,X27))|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).
% 0.12/0.37  cnf(c_0_25, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))))), inference(rw,[status(thm)],[c_0_20, c_0_19])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk3_0)))))), inference(rw,[status(thm)],[c_0_21, c_0_19])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_22, c_0_19])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(k2_struct_0(esk3_0))))), inference(rw,[status(thm)],[c_0_23, c_0_19])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_32, plain, ![X13]:(~l1_struct_0(X13)|k2_struct_0(X13)=u1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.12/0.37  fof(c_0_33, plain, ![X14]:(~l1_pre_topc(X14)|l1_struct_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.37  cnf(c_0_34, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))=esk4_0|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  fof(c_0_38, plain, ![X18, X19, X20]:(((~v2_struct_0(k3_yellow19(X18,X19,X20))|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))&(v6_waybel_0(k3_yellow19(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))))))&(l1_waybel_0(k3_yellow19(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.12/0.37  cnf(c_0_39, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_40, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_41, plain, (r2_waybel_7(X2,k2_yellow19(X2,X3),X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r2_hidden(X1,k10_yellow_6(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (~r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|r2_hidden(X1,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|~r2_waybel_7(esk3_0,esk4_0,X1)|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])]), c_0_30])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_45, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_46, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.37  fof(c_0_47, plain, ![X9]:m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.12/0.37  fof(c_0_48, plain, ![X8]:k2_subset_1(X8)=X8, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,X1)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)|~l1_struct_0(esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_35]), c_0_36]), c_0_37])]), c_0_30])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,k10_yellow_6(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0)))|r2_waybel_7(esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.12/0.37  cnf(c_0_52, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_19]), c_0_19]), c_0_19])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (v13_waybel_0(esk4_0,k3_lattice3(k1_lattice3(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (v2_waybel_0(esk4_0,k3_lattice3(k1_lattice3(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_29, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_56, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.37  cnf(c_0_57, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.37  fof(c_0_58, plain, ![X24, X25, X26]:(((~v2_struct_0(k3_yellow19(X24,X25,X26))|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))&(v6_waybel_0(k3_yellow19(X24,X25,X26),X24)|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25)))))))&(v7_waybel_0(k3_yellow19(X24,X25,X26))|(v2_struct_0(X24)|~l1_struct_0(X24)|v1_xboole_0(X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v1_xboole_0(X26)|~v1_subset_1(X26,u1_struct_0(k3_yellow_1(X25)))|~v2_waybel_0(X26,k3_yellow_1(X25))|~v13_waybel_0(X26,k3_yellow_1(X25))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X25))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0),esk3_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_49, c_0_50]), c_0_44])])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0),esk3_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0),X1)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])]), c_0_31])).
% 0.12/0.37  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.37  cnf(c_0_63, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0),esk3_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60, c_0_61]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_66, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_19]), c_0_19]), c_0_19]), c_0_19])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (v1_subset_1(esk4_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27, c_0_46]), c_0_37])])).
% 0.12/0.37  fof(c_0_68, plain, ![X21, X22, X23]:((((~v2_struct_0(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22))))))&(v3_orders_2(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))))))&(v4_orders_2(k3_yellow19(X21,X22,X23))|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22)))))))&(v6_waybel_0(k3_yellow19(X21,X22,X23),X21)|(v2_struct_0(X21)|~l1_struct_0(X21)|v1_xboole_0(X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v1_xboole_0(X23)|~v2_waybel_0(X23,k3_yellow_1(X22))|~v13_waybel_0(X23,k3_yellow_1(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X22))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64, c_0_61]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~v7_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_53]), c_0_67]), c_0_54]), c_0_55])]), c_0_31])).
% 0.12/0.37  cnf(c_0_72, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~v7_waybel_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_74, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_71]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_75, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_19]), c_0_19]), c_0_19])).
% 0.12/0.37  cnf(c_0_76, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73, c_0_71]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_77, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_78, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~v4_orders_2(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_79, negated_conjecture, (v4_orders_2(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_53]), c_0_54]), c_0_55])]), c_0_31])).
% 0.12/0.37  cnf(c_0_80, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~v4_orders_2(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_46]), c_0_37])])).
% 0.12/0.37  fof(c_0_81, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.12/0.37  fof(c_0_82, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.37  cnf(c_0_83, plain, (v1_xboole_0(X3)|v1_xboole_0(X2)|v2_struct_0(X1)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_19]), c_0_19]), c_0_19])).
% 0.12/0.37  cnf(c_0_84, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78, c_0_79]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_85, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80, c_0_79]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_86, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.12/0.37  cnf(c_0_87, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.12/0.37  fof(c_0_88, plain, ![X15]:(((m1_subset_1(esk2_1(X15),k1_zfmisc_1(u1_struct_0(X15)))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~v1_xboole_0(esk2_1(X15))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&(v4_pre_topc(esk2_1(X15),X15)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.12/0.37  cnf(c_0_89, negated_conjecture, (v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk3_0))|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk3_0),esk4_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_53]), c_0_54]), c_0_55])]), c_0_31])).
% 0.12/0.37  cnf(c_0_90, negated_conjecture, (v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_91, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v2_struct_0(k3_yellow19(esk3_0,u1_struct_0(esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85, c_0_46]), c_0_37])])).
% 0.12/0.37  cnf(c_0_92, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_86, c_0_87])).
% 0.12/0.37  cnf(c_0_93, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.12/0.37  cnf(c_0_94, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~r2_waybel_7(esk3_0,esk4_0,esk5_0)|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89, c_0_90]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_95, negated_conjecture, (r2_waybel_7(esk3_0,esk4_0,esk5_0)|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89, c_0_91]), c_0_62])]), c_0_30])).
% 0.12/0.37  cnf(c_0_96, plain, (v2_struct_0(X1)|~v1_xboole_0(esk2_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.12/0.37  cnf(c_0_97, plain, (v2_struct_0(X1)|v1_xboole_0(esk2_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_92, c_0_93])).
% 0.12/0.37  cnf(c_0_98, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk3_0)), inference(pm,[status(thm)],[c_0_94, c_0_95])).
% 0.12/0.37  cnf(c_0_99, negated_conjecture, (~v1_xboole_0(esk2_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_96]), c_0_36]), c_0_37])])).
% 0.12/0.37  cnf(c_0_100, negated_conjecture, (~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_97, c_0_98]), c_0_36]), c_0_37])]), c_0_30]), c_0_99])).
% 0.12/0.37  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100, c_0_40]), c_0_37])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 102
% 0.12/0.37  # Proof object clause steps            : 73
% 0.12/0.37  # Proof object formula steps           : 29
% 0.12/0.37  # Proof object conjectures             : 51
% 0.12/0.37  # Proof object clause conjectures      : 48
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 27
% 0.12/0.37  # Proof object initial formulas used   : 14
% 0.12/0.37  # Proof object generating inferences   : 36
% 0.12/0.37  # Proof object simplifying inferences  : 115
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 14
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 35
% 0.12/0.37  # Removed in clause preprocessing      : 2
% 0.12/0.37  # Initial clauses in saturation        : 33
% 0.12/0.37  # Processed clauses                    : 124
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 14
% 0.12/0.37  # ...remaining for further processing  : 110
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 19
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 135
% 0.12/0.37  # ...of the previous two non-trivial   : 128
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 135
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 91
% 0.12/0.37  #    Positive orientable unit clauses  : 12
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 6
% 0.12/0.37  #    Non-unit-clauses                  : 73
% 0.12/0.37  # Current number of unprocessed clauses: 29
% 0.12/0.37  # ...number of literals in the above   : 243
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 21
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 1048
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 117
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 32
% 0.12/0.37  # Unit Clause-clause subsumption calls : 39
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 4
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 7461
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.037 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.043 s
% 0.12/0.37  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
