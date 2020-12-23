%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:00 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   91 (1810 expanded)
%              Number of clauses        :   66 ( 718 expanded)
%              Number of leaves         :   12 ( 459 expanded)
%              Depth                    :   13
%              Number of atoms          :  455 (9055 expanded)
%              Number of equality atoms :   12 ( 477 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   3 average)
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | v1_xboole_0(X29)
      | ~ v1_subset_1(X29,u1_struct_0(k3_yellow_1(k2_struct_0(X28))))
      | ~ v2_waybel_0(X29,k3_yellow_1(k2_struct_0(X28)))
      | ~ v13_waybel_0(X29,k3_yellow_1(k2_struct_0(X28)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X28)))))
      | X29 = k2_yellow19(X28,k3_yellow19(X28,k2_struct_0(X28),X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_14,plain,(
    ! [X15] : k3_yellow_1(X15) = k3_lattice3(k1_lattice3(X15)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_17,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(k2_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

fof(c_0_18,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v2_struct_0(k3_yellow19(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v1_xboole_0(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v1_xboole_0(X21)
        | ~ v2_waybel_0(X21,k3_yellow_1(X20))
        | ~ v13_waybel_0(X21,k3_yellow_1(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))) )
      & ( v3_orders_2(k3_yellow19(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v1_xboole_0(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v1_xboole_0(X21)
        | ~ v2_waybel_0(X21,k3_yellow_1(X20))
        | ~ v13_waybel_0(X21,k3_yellow_1(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))) )
      & ( v4_orders_2(k3_yellow19(X19,X20,X21))
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v1_xboole_0(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v1_xboole_0(X21)
        | ~ v2_waybel_0(X21,k3_yellow_1(X20))
        | ~ v13_waybel_0(X21,k3_yellow_1(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))) )
      & ( v6_waybel_0(k3_yellow19(X19,X20,X21),X19)
        | v2_struct_0(X19)
        | ~ l1_struct_0(X19)
        | v1_xboole_0(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | v1_xboole_0(X21)
        | ~ v2_waybel_0(X21,k3_yellow_1(X20))
        | ~ v13_waybel_0(X21,k3_yellow_1(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_31,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_struct_0(k3_yellow19(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v1_xboole_0(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v1_xboole_0(X24)
        | ~ v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))
        | ~ v2_waybel_0(X24,k3_yellow_1(X23))
        | ~ v13_waybel_0(X24,k3_yellow_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))) )
      & ( v6_waybel_0(k3_yellow19(X22,X23,X24),X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v1_xboole_0(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v1_xboole_0(X24)
        | ~ v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))
        | ~ v2_waybel_0(X24,k3_yellow_1(X23))
        | ~ v13_waybel_0(X24,k3_yellow_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))) )
      & ( v7_waybel_0(k3_yellow19(X22,X23,X24))
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22)
        | v1_xboole_0(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v1_xboole_0(X24)
        | ~ v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))
        | ~ v2_waybel_0(X24,k3_yellow_1(X23))
        | ~ v13_waybel_0(X24,k3_yellow_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

fof(c_0_32,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r3_waybel_9(X25,X26,X27)
        | r1_waybel_7(X25,k2_yellow19(X25,X26),X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ r1_waybel_7(X25,k2_yellow19(X25,X26),X27)
        | r3_waybel_9(X25,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_33,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_41,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_43,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_47,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v2_struct_0(k3_yellow19(X16,X17,X18))
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v1_xboole_0(X18)
        | ~ v2_waybel_0(X18,k3_yellow_1(X17))
        | ~ v13_waybel_0(X18,k3_yellow_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))) )
      & ( v6_waybel_0(k3_yellow19(X16,X17,X18),X16)
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v1_xboole_0(X18)
        | ~ v2_waybel_0(X18,k3_yellow_1(X17))
        | ~ v13_waybel_0(X18,k3_yellow_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))) )
      & ( l1_waybel_0(k3_yellow19(X16,X17,X18),X16)
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | v1_xboole_0(X18)
        | ~ v2_waybel_0(X18,k3_yellow_1(X17))
        | ~ v13_waybel_0(X18,k3_yellow_1(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)
    | r1_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( k2_yellow19(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_40])])).

cnf(c_0_55,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_40])])).

cnf(c_0_56,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_29]),c_0_40])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_39])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_60,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_20]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_40])])).

cnf(c_0_62,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( r1_waybel_7(esk2_0,k2_yellow19(esk2_0,X1),esk4_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk2_0,X1,esk4_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_26])]),c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_29]),c_0_40])])).

cnf(c_0_66,negated_conjecture,
    ( k2_yellow19(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_29]),c_0_40])])).

cnf(c_0_67,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])]),c_0_57]),c_0_38])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_54]),c_0_61]),c_0_55]),c_0_56])]),c_0_57]),c_0_38])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_73,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_40])]),c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_40])]),c_0_39])).

cnf(c_0_75,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0),X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_54]),c_0_55]),c_0_56])]),c_0_57]),c_0_38])).

cnf(c_0_76,negated_conjecture,
    ( ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)
    | ~ r1_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_34]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_78,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),c_0_74])])).

cnf(c_0_79,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_68]),c_0_40])]),c_0_39])).

cnf(c_0_80,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_29]),c_0_40])]),c_0_57])).

cnf(c_0_83,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_84,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),X1)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,X1)
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_66]),c_0_50]),c_0_26])]),c_0_39]),c_0_74]),c_0_73])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_40])])).

cnf(c_0_86,negated_conjecture,
    ( r1_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_40]),c_0_68])]),c_0_39])).

cnf(c_0_87,negated_conjecture,
    ( r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),X1)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ r1_waybel_7(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_79])])).

cnf(c_0_88,negated_conjecture,
    ( ~ r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_86]),c_0_49])]),c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_89]),c_0_40]),c_0_68])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:29:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.15/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.031 s
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 0.15/0.39  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.15/0.39  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.15/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.15/0.39  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.15/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.15/0.39  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.15/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.15/0.39  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.15/0.39  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 0.15/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.15/0.39  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.15/0.39  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.15/0.39  fof(c_0_13, plain, ![X28, X29]:(v2_struct_0(X28)|~l1_struct_0(X28)|(v1_xboole_0(X29)|~v1_subset_1(X29,u1_struct_0(k3_yellow_1(k2_struct_0(X28))))|~v2_waybel_0(X29,k3_yellow_1(k2_struct_0(X28)))|~v13_waybel_0(X29,k3_yellow_1(k2_struct_0(X28)))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X28)))))|X29=k2_yellow19(X28,k3_yellow19(X28,k2_struct_0(X28),X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.15/0.39  fof(c_0_14, plain, ![X15]:k3_yellow_1(X15)=k3_lattice3(k1_lattice3(X15)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.15/0.39  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((((~v1_xboole_0(esk3_0)&v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))&v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))))&v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))))&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|~r1_waybel_7(esk2_0,esk3_0,esk4_0))&(r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|r1_waybel_7(esk2_0,esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.15/0.39  fof(c_0_16, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.15/0.39  fof(c_0_17, plain, ![X14]:(v2_struct_0(X14)|~l1_struct_0(X14)|~v1_xboole_0(k2_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.15/0.39  fof(c_0_18, plain, ![X12]:(~l1_struct_0(X12)|k2_struct_0(X12)=u1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.15/0.39  cnf(c_0_19, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_20, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_22, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_23, negated_conjecture, (v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_24, negated_conjecture, (v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_25, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.39  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  fof(c_0_27, plain, ![X19, X20, X21]:((((~v2_struct_0(k3_yellow19(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20))))))&(v3_orders_2(k3_yellow19(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))))))&(v4_orders_2(k3_yellow19(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))))))&(v6_waybel_0(k3_yellow19(X19,X20,X21),X19)|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.15/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.39  cnf(c_0_29, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.39  fof(c_0_30, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.15/0.39  fof(c_0_31, plain, ![X22, X23, X24]:(((~v2_struct_0(k3_yellow19(X22,X23,X24))|(v2_struct_0(X22)|~l1_struct_0(X22)|v1_xboole_0(X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v1_xboole_0(X24)|~v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))|~v2_waybel_0(X24,k3_yellow_1(X23))|~v13_waybel_0(X24,k3_yellow_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23))))))&(v6_waybel_0(k3_yellow19(X22,X23,X24),X22)|(v2_struct_0(X22)|~l1_struct_0(X22)|v1_xboole_0(X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v1_xboole_0(X24)|~v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))|~v2_waybel_0(X24,k3_yellow_1(X23))|~v13_waybel_0(X24,k3_yellow_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))))))&(v7_waybel_0(k3_yellow19(X22,X23,X24))|(v2_struct_0(X22)|~l1_struct_0(X22)|v1_xboole_0(X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v1_xboole_0(X24)|~v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))|~v2_waybel_0(X24,k3_yellow_1(X23))|~v13_waybel_0(X24,k3_yellow_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.15/0.39  fof(c_0_32, plain, ![X25, X26, X27]:((~r3_waybel_9(X25,X26,X27)|r1_waybel_7(X25,k2_yellow19(X25,X26),X27)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~r1_waybel_7(X25,k2_yellow19(X25,X26),X27)|r3_waybel_9(X25,X26,X27)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.15/0.39  cnf(c_0_33, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20]), c_0_20]), c_0_20]), c_0_20])).
% 0.15/0.39  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 0.15/0.39  cnf(c_0_35, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))))), inference(rw,[status(thm)],[c_0_22, c_0_20])).
% 0.15/0.39  cnf(c_0_36, negated_conjecture, (v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_23, c_0_20])).
% 0.15/0.39  cnf(c_0_37, negated_conjecture, (v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_24, c_0_20])).
% 0.15/0.39  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_40, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.15/0.39  cnf(c_0_41, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.39  cnf(c_0_42, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.15/0.39  fof(c_0_43, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.15/0.39  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.15/0.39  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.15/0.39  cnf(c_0_46, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.15/0.39  fof(c_0_47, plain, ![X16, X17, X18]:(((~v2_struct_0(k3_yellow19(X16,X17,X18))|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17))))))&(v6_waybel_0(k3_yellow19(X16,X17,X18),X16)|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))))))&(l1_waybel_0(k3_yellow19(X16,X17,X18),X16)|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.15/0.39  cnf(c_0_48, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.15/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_51, negated_conjecture, (r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|r1_waybel_7(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_52, negated_conjecture, (k2_yellow19(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38]), c_0_39]), c_0_40])])).
% 0.15/0.39  cnf(c_0_53, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_20]), c_0_20]), c_0_20])).
% 0.15/0.39  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_29]), c_0_40])])).
% 0.15/0.39  cnf(c_0_55, negated_conjecture, (v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_29]), c_0_40])])).
% 0.15/0.39  cnf(c_0_56, negated_conjecture, (v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_29]), c_0_40])])).
% 0.15/0.39  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_39])).
% 0.15/0.39  cnf(c_0_58, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.15/0.39  cnf(c_0_59, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.15/0.39  cnf(c_0_60, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_20]), c_0_20]), c_0_20]), c_0_20])).
% 0.15/0.39  cnf(c_0_61, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_40])])).
% 0.15/0.39  cnf(c_0_62, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  cnf(c_0_63, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.15/0.39  cnf(c_0_64, negated_conjecture, (r1_waybel_7(esk2_0,k2_yellow19(esk2_0,X1),esk4_0)|v2_struct_0(X1)|~r3_waybel_9(esk2_0,X1,esk4_0)|~v7_waybel_0(X1)|~v4_orders_2(X1)|~l1_waybel_0(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_26])]), c_0_39])).
% 0.15/0.39  cnf(c_0_65, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_29]), c_0_40])])).
% 0.15/0.39  cnf(c_0_66, negated_conjecture, (k2_yellow19(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_29]), c_0_40])])).
% 0.15/0.39  cnf(c_0_67, negated_conjecture, (v4_orders_2(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])]), c_0_57]), c_0_38])).
% 0.15/0.39  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.15/0.39  cnf(c_0_69, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_54]), c_0_61]), c_0_55]), c_0_56])]), c_0_57]), c_0_38])).
% 0.15/0.39  cnf(c_0_70, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_20]), c_0_20]), c_0_20])).
% 0.15/0.39  cnf(c_0_71, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_20]), c_0_20]), c_0_20])).
% 0.15/0.39  cnf(c_0_72, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.15/0.39  cnf(c_0_73, negated_conjecture, (v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_40])]), c_0_39])).
% 0.15/0.39  cnf(c_0_74, negated_conjecture, (v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_40])]), c_0_39])).
% 0.15/0.39  cnf(c_0_75, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0),X1)|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_54]), c_0_55]), c_0_56])]), c_0_57]), c_0_38])).
% 0.15/0.39  cnf(c_0_76, negated_conjecture, (~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk4_0)|~r1_waybel_7(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_77, negated_conjecture, (v1_xboole_0(k2_struct_0(esk2_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_34]), c_0_36]), c_0_37])]), c_0_38])).
% 0.15/0.39  cnf(c_0_78, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])]), c_0_74])])).
% 0.15/0.39  cnf(c_0_79, negated_conjecture, (l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_68]), c_0_40])]), c_0_39])).
% 0.15/0.39  cnf(c_0_80, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.15/0.39  cnf(c_0_81, negated_conjecture, (~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0)|~l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_76, c_0_29])).
% 0.15/0.39  cnf(c_0_82, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_29]), c_0_40])]), c_0_57])).
% 0.15/0.39  cnf(c_0_83, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 0.15/0.39  cnf(c_0_84, negated_conjecture, (r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),X1)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~r1_waybel_7(esk2_0,esk3_0,X1)|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_66]), c_0_50]), c_0_26])]), c_0_39]), c_0_74]), c_0_73])])).
% 0.15/0.39  cnf(c_0_85, negated_conjecture, (~r1_waybel_7(esk2_0,esk3_0,esk4_0)|~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_40])])).
% 0.15/0.39  cnf(c_0_86, negated_conjecture, (r1_waybel_7(esk2_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_40]), c_0_68])]), c_0_39])).
% 0.15/0.39  cnf(c_0_87, negated_conjecture, (r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),X1)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~r1_waybel_7(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_79])])).
% 0.15/0.39  cnf(c_0_88, negated_conjecture, (~r3_waybel_9(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.15/0.39  cnf(c_0_89, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_86]), c_0_49])]), c_0_88])).
% 0.15/0.39  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_89]), c_0_40]), c_0_68])]), c_0_39]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 91
% 0.15/0.39  # Proof object clause steps            : 66
% 0.15/0.39  # Proof object formula steps           : 25
% 0.15/0.39  # Proof object conjectures             : 47
% 0.15/0.39  # Proof object clause conjectures      : 44
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 25
% 0.15/0.39  # Proof object initial formulas used   : 12
% 0.15/0.39  # Proof object generating inferences   : 27
% 0.15/0.39  # Proof object simplifying inferences  : 110
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 12
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 33
% 0.15/0.39  # Removed in clause preprocessing      : 1
% 0.15/0.39  # Initial clauses in saturation        : 32
% 0.15/0.39  # Processed clauses                    : 114
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 23
% 0.15/0.39  # ...remaining for further processing  : 91
% 0.15/0.39  # Other redundant clauses eliminated   : 0
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 0
% 0.15/0.39  # Backward-rewritten                   : 13
% 0.15/0.39  # Generated clauses                    : 99
% 0.15/0.39  # ...of the previous two non-trivial   : 99
% 0.15/0.39  # Contextual simplify-reflections      : 0
% 0.15/0.39  # Paramodulations                      : 97
% 0.15/0.39  # Factorizations                       : 2
% 0.15/0.39  # Equation resolutions                 : 0
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 78
% 0.15/0.39  #    Positive orientable unit clauses  : 25
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 5
% 0.15/0.39  #    Non-unit-clauses                  : 48
% 0.15/0.39  # Current number of unprocessed clauses: 17
% 0.15/0.39  # ...number of literals in the above   : 70
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 14
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 2239
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 253
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 22
% 0.15/0.39  # Unit Clause-clause subsumption calls : 108
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 23
% 0.15/0.39  # BW rewrite match successes           : 5
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 7590
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.040 s
% 0.15/0.39  # System time              : 0.005 s
% 0.15/0.39  # Total time               : 0.045 s
% 0.15/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
