%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:01 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 825 expanded)
%              Number of clauses        :   67 ( 324 expanded)
%              Number of leaves         :   13 ( 212 expanded)
%              Depth                    :   15
%              Number of atoms          :  509 (4162 expanded)
%              Number of equality atoms :   17 ( 294 expanded)
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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | v1_xboole_0(X25)
      | ~ v1_subset_1(X25,u1_struct_0(k3_yellow_1(k2_struct_0(X24))))
      | ~ v2_waybel_0(X25,k3_yellow_1(k2_struct_0(X24)))
      | ~ v13_waybel_0(X25,k3_yellow_1(k2_struct_0(X24)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X24)))))
      | X25 = k2_yellow19(X24,k3_yellow19(X24,k2_struct_0(X24),X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_15,plain,(
    ! [X9] : k3_yellow_1(X9) = k3_lattice3(k1_lattice3(X9)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_16,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v2_struct_0(k3_yellow19(X12,X13,X14))
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v1_xboole_0(X14)
        | ~ v2_waybel_0(X14,k3_yellow_1(X13))
        | ~ v13_waybel_0(X14,k3_yellow_1(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X13)))) )
      & ( v6_waybel_0(k3_yellow19(X12,X13,X14),X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v1_xboole_0(X14)
        | ~ v2_waybel_0(X14,k3_yellow_1(X13))
        | ~ v13_waybel_0(X14,k3_yellow_1(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X13)))) )
      & ( l1_waybel_0(k3_yellow19(X12,X13,X14),X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12)
        | v1_xboole_0(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v1_xboole_0(X14)
        | ~ v2_waybel_0(X14,k3_yellow_1(X13))
        | ~ v13_waybel_0(X14,k3_yellow_1(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X13)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_struct_0(k3_yellow19(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v1_subset_1(X20,u1_struct_0(k3_yellow_1(X19)))
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( v6_waybel_0(k3_yellow19(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v1_subset_1(X20,u1_struct_0(k3_yellow_1(X19)))
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( v7_waybel_0(k3_yellow19(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v1_subset_1(X20,u1_struct_0(k3_yellow_1(X19)))
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] :
      ( ( ~ r3_waybel_9(X21,X22,X23)
        | r1_waybel_7(X21,k2_yellow19(X21,X22),X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_waybel_7(X21,k2_yellow19(X21,X22),X23)
        | r3_waybel_9(X21,X22,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | v2_struct_0(X22)
        | ~ v4_orders_2(X22)
        | ~ v7_waybel_0(X22)
        | ~ l1_waybel_0(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_26,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_34,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | k2_struct_0(X6) = u1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_35,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_36,plain,(
    ! [X10,X11] :
      ( ( ~ v1_subset_1(X11,X10)
        | X11 != X10
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) )
      & ( X11 = X10
        | v1_subset_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

fof(c_0_37,plain,(
    ! [X4] : m1_subset_1(k2_subset_1(X4),k1_zfmisc_1(X4)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_38,plain,(
    ! [X5] : ~ v1_subset_1(k2_subset_1(X5),X5) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_40,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v2_struct_0(k3_yellow19(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v1_xboole_0(X17)
        | ~ v2_waybel_0(X17,k3_yellow_1(X16))
        | ~ v13_waybel_0(X17,k3_yellow_1(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16)))) )
      & ( v3_orders_2(k3_yellow19(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v1_xboole_0(X17)
        | ~ v2_waybel_0(X17,k3_yellow_1(X16))
        | ~ v13_waybel_0(X17,k3_yellow_1(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16)))) )
      & ( v4_orders_2(k3_yellow19(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v1_xboole_0(X17)
        | ~ v2_waybel_0(X17,k3_yellow_1(X16))
        | ~ v13_waybel_0(X17,k3_yellow_1(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16)))) )
      & ( v6_waybel_0(k3_yellow19(X15,X16,X17),X15)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v1_xboole_0(X17)
        | ~ v2_waybel_0(X17,k3_yellow_1(X16))
        | ~ v13_waybel_0(X17,k3_yellow_1(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_46,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_52,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44])]),c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45,c_0_27]),c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_59,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_60,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,X1)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_42]),c_0_43]),c_0_44])]),c_0_32])).

cnf(c_0_64,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_67,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_59]),c_0_44])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61,c_0_59]),c_0_44])])).

cnf(c_0_70,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_27]),c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_71,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_63,c_0_64]),c_0_57])])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65,c_0_27]),c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),c_0_32])).

cnf(c_0_74,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_68]),c_0_32])).

cnf(c_0_75,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_59]),c_0_44])])).

cnf(c_0_76,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71,c_0_67]),c_0_68])]),c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_59]),c_0_44])])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_68]),c_0_32])).

cnf(c_0_80,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_76,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_68]),c_0_32])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_80,c_0_79])).

fof(c_0_84,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_85,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_81,c_0_83])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85,c_0_59]),c_0_44])])).

cnf(c_0_89,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_59]),c_0_44])])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_87,c_0_88]),c_0_32])).

cnf(c_0_91,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_87,c_0_89]),c_0_32])).

cnf(c_0_92,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92,c_0_47]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n024.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:25:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.18/0.39  # and selection function NoSelection.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.041 s
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_yellow19)).
% 0.18/0.39  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 0.18/0.39  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.18/0.39  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.18/0.39  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.18/0.39  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow19)).
% 0.18/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.18/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.18/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.18/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.18/0.39  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.18/0.39  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.18/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.18/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.18/0.40  fof(c_0_14, plain, ![X24, X25]:(v2_struct_0(X24)|~l1_struct_0(X24)|(v1_xboole_0(X25)|~v1_subset_1(X25,u1_struct_0(k3_yellow_1(k2_struct_0(X24))))|~v2_waybel_0(X25,k3_yellow_1(k2_struct_0(X24)))|~v13_waybel_0(X25,k3_yellow_1(k2_struct_0(X24)))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X24)))))|X25=k2_yellow19(X24,k3_yellow19(X24,k2_struct_0(X24),X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.18/0.40  fof(c_0_15, plain, ![X9]:k3_yellow_1(X9)=k3_lattice3(k1_lattice3(X9)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.18/0.40  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((((~v1_xboole_0(esk2_0)&v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))&v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&((~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0))&(r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.18/0.40  cnf(c_0_17, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.40  cnf(c_0_18, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_20, negated_conjecture, (v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_21, negated_conjecture, (v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_22, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  fof(c_0_23, plain, ![X12, X13, X14]:(((~v2_struct_0(k3_yellow19(X12,X13,X14))|(v2_struct_0(X12)|~l1_struct_0(X12)|v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|v1_xboole_0(X14)|~v2_waybel_0(X14,k3_yellow_1(X13))|~v13_waybel_0(X14,k3_yellow_1(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X13))))))&(v6_waybel_0(k3_yellow19(X12,X13,X14),X12)|(v2_struct_0(X12)|~l1_struct_0(X12)|v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|v1_xboole_0(X14)|~v2_waybel_0(X14,k3_yellow_1(X13))|~v13_waybel_0(X14,k3_yellow_1(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X13)))))))&(l1_waybel_0(k3_yellow19(X12,X13,X14),X12)|(v2_struct_0(X12)|~l1_struct_0(X12)|v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|v1_xboole_0(X14)|~v2_waybel_0(X14,k3_yellow_1(X13))|~v13_waybel_0(X14,k3_yellow_1(X13))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X13))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.18/0.40  fof(c_0_24, plain, ![X18, X19, X20]:(((~v2_struct_0(k3_yellow19(X18,X19,X20))|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v1_subset_1(X20,u1_struct_0(k3_yellow_1(X19)))|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))&(v6_waybel_0(k3_yellow19(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v1_subset_1(X20,u1_struct_0(k3_yellow_1(X19)))|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))))))&(v7_waybel_0(k3_yellow19(X18,X19,X20))|(v2_struct_0(X18)|~l1_struct_0(X18)|v1_xboole_0(X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|v1_xboole_0(X20)|~v1_subset_1(X20,u1_struct_0(k3_yellow_1(X19)))|~v2_waybel_0(X20,k3_yellow_1(X19))|~v13_waybel_0(X20,k3_yellow_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.18/0.40  fof(c_0_25, plain, ![X21, X22, X23]:((~r3_waybel_9(X21,X22,X23)|r1_waybel_7(X21,k2_yellow19(X21,X22),X23)|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(~r1_waybel_7(X21,k2_yellow19(X21,X22),X23)|r3_waybel_9(X21,X22,X23)|~m1_subset_1(X23,u1_struct_0(X21))|(v2_struct_0(X22)|~v4_orders_2(X22)|~v7_waybel_0(X22)|~l1_waybel_0(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.18/0.40  cnf(c_0_26, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.18/0.40  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.18/0.40  cnf(c_0_28, negated_conjecture, (v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.18/0.40  cnf(c_0_29, negated_conjecture, (v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_21, c_0_18])).
% 0.18/0.40  cnf(c_0_30, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))), inference(rw,[status(thm)],[c_0_22, c_0_18])).
% 0.18/0.40  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_33, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.40  fof(c_0_34, plain, ![X6]:(~l1_struct_0(X6)|k2_struct_0(X6)=u1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.18/0.40  fof(c_0_35, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.18/0.40  fof(c_0_36, plain, ![X10, X11]:((~v1_subset_1(X11,X10)|X11!=X10|~m1_subset_1(X11,k1_zfmisc_1(X10)))&(X11=X10|v1_subset_1(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.18/0.40  fof(c_0_37, plain, ![X4]:m1_subset_1(k2_subset_1(X4),k1_zfmisc_1(X4)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.18/0.40  fof(c_0_38, plain, ![X5]:~v1_subset_1(k2_subset_1(X5),X5), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.18/0.40  cnf(c_0_39, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.40  fof(c_0_40, plain, ![X15, X16, X17]:((((~v2_struct_0(k3_yellow19(X15,X16,X17))|(v2_struct_0(X15)|~l1_struct_0(X15)|v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|v1_xboole_0(X17)|~v2_waybel_0(X17,k3_yellow_1(X16))|~v13_waybel_0(X17,k3_yellow_1(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16))))))&(v3_orders_2(k3_yellow19(X15,X16,X17))|(v2_struct_0(X15)|~l1_struct_0(X15)|v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|v1_xboole_0(X17)|~v2_waybel_0(X17,k3_yellow_1(X16))|~v13_waybel_0(X17,k3_yellow_1(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16)))))))&(v4_orders_2(k3_yellow19(X15,X16,X17))|(v2_struct_0(X15)|~l1_struct_0(X15)|v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|v1_xboole_0(X17)|~v2_waybel_0(X17,k3_yellow_1(X16))|~v13_waybel_0(X17,k3_yellow_1(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16)))))))&(v6_waybel_0(k3_yellow19(X15,X16,X17),X15)|(v2_struct_0(X15)|~l1_struct_0(X15)|v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|v1_xboole_0(X17)|~v2_waybel_0(X17,k3_yellow_1(X16))|~v13_waybel_0(X17,k3_yellow_1(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X16))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.18/0.40  cnf(c_0_41, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.40  cnf(c_0_42, negated_conjecture, (k2_yellow19(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))=esk2_0|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31]), c_0_32])).
% 0.18/0.40  cnf(c_0_43, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_44, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_45, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_18]), c_0_18]), c_0_18])).
% 0.18/0.40  cnf(c_0_46, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.40  cnf(c_0_47, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.40  cnf(c_0_48, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.40  cnf(c_0_49, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.40  cnf(c_0_50, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.40  cnf(c_0_51, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.18/0.40  cnf(c_0_52, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.40  cnf(c_0_53, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.40  cnf(c_0_54, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.40  cnf(c_0_55, negated_conjecture, (~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_56, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,X1)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44])]), c_0_32])).
% 0.18/0.40  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_58, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45, c_0_27]), c_0_28]), c_0_29])]), c_0_31])).
% 0.18/0.40  cnf(c_0_59, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.40  cnf(c_0_60, plain, (k2_subset_1(X1)=X1), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.18/0.40  cnf(c_0_61, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.18/0.40  cnf(c_0_62, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_18]), c_0_18]), c_0_18])).
% 0.18/0.40  cnf(c_0_63, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,X1)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),X1)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_42]), c_0_43]), c_0_44])]), c_0_32])).
% 0.18/0.40  cnf(c_0_64, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  cnf(c_0_65, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_18]), c_0_18]), c_0_18])).
% 0.18/0.40  cnf(c_0_66, negated_conjecture, (v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.18/0.40  cnf(c_0_67, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_59]), c_0_44])])).
% 0.18/0.40  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_49, c_0_60])).
% 0.18/0.40  cnf(c_0_69, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61, c_0_59]), c_0_44])])).
% 0.18/0.40  cnf(c_0_70, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_27]), c_0_28]), c_0_29])]), c_0_31])).
% 0.18/0.40  cnf(c_0_71, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_63, c_0_64]), c_0_57])])).
% 0.18/0.40  cnf(c_0_72, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65, c_0_27]), c_0_28]), c_0_29])]), c_0_31])).
% 0.18/0.40  cnf(c_0_73, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), c_0_32])).
% 0.18/0.40  cnf(c_0_74, negated_conjecture, (v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_68]), c_0_32])).
% 0.18/0.40  cnf(c_0_75, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_59]), c_0_44])])).
% 0.18/0.40  cnf(c_0_76, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71, c_0_67]), c_0_68])]), c_0_32])).
% 0.18/0.40  cnf(c_0_77, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_59]), c_0_44])])).
% 0.18/0.40  cnf(c_0_78, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_73, c_0_74])).
% 0.18/0.40  cnf(c_0_79, negated_conjecture, (v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_68]), c_0_32])).
% 0.18/0.40  cnf(c_0_80, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_76, c_0_74])).
% 0.18/0.40  cnf(c_0_81, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|~v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_68]), c_0_32])).
% 0.18/0.40  cnf(c_0_82, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_78, c_0_79])).
% 0.18/0.40  cnf(c_0_83, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_80, c_0_79])).
% 0.18/0.40  fof(c_0_84, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.18/0.40  cnf(c_0_85, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_81, c_0_82])).
% 0.18/0.40  cnf(c_0_86, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_81, c_0_83])).
% 0.18/0.40  cnf(c_0_87, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.18/0.40  cnf(c_0_88, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85, c_0_59]), c_0_44])])).
% 0.18/0.40  cnf(c_0_89, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_59]), c_0_44])])).
% 0.18/0.40  cnf(c_0_90, negated_conjecture, (~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_87, c_0_88]), c_0_32])).
% 0.18/0.40  cnf(c_0_91, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_87, c_0_89]), c_0_32])).
% 0.18/0.40  cnf(c_0_92, negated_conjecture, (~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_90, c_0_91])).
% 0.18/0.40  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92, c_0_47]), c_0_44])]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 94
% 0.18/0.40  # Proof object clause steps            : 67
% 0.18/0.40  # Proof object formula steps           : 27
% 0.18/0.40  # Proof object conjectures             : 48
% 0.18/0.40  # Proof object clause conjectures      : 45
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 25
% 0.18/0.40  # Proof object initial formulas used   : 13
% 0.18/0.40  # Proof object generating inferences   : 32
% 0.18/0.40  # Proof object simplifying inferences  : 83
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 13
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 32
% 0.18/0.40  # Removed in clause preprocessing      : 1
% 0.18/0.40  # Initial clauses in saturation        : 31
% 0.18/0.40  # Processed clauses                    : 142
% 0.18/0.40  # ...of these trivial                  : 0
% 0.18/0.40  # ...subsumed                          : 17
% 0.18/0.40  # ...remaining for further processing  : 125
% 0.18/0.40  # Other redundant clauses eliminated   : 0
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 15
% 0.18/0.40  # Backward-rewritten                   : 2
% 0.18/0.40  # Generated clauses                    : 139
% 0.18/0.40  # ...of the previous two non-trivial   : 134
% 0.18/0.40  # Contextual simplify-reflections      : 0
% 0.18/0.40  # Paramodulations                      : 139
% 0.18/0.40  # Factorizations                       : 0
% 0.18/0.40  # Equation resolutions                 : 0
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 108
% 0.18/0.40  #    Positive orientable unit clauses  : 13
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 6
% 0.18/0.40  #    Non-unit-clauses                  : 89
% 0.18/0.40  # Current number of unprocessed clauses: 16
% 0.18/0.40  # ...number of literals in the above   : 130
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 18
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 996
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 124
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 28
% 0.18/0.40  # Unit Clause-clause subsumption calls : 83
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 8
% 0.18/0.40  # BW rewrite match successes           : 1
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 7809
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.055 s
% 0.18/0.40  # System time              : 0.008 s
% 0.18/0.40  # Total time               : 0.063 s
% 0.18/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
