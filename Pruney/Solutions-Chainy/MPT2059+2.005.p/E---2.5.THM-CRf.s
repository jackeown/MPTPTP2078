%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:02 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 (1740 expanded)
%              Number of clauses        :   65 ( 686 expanded)
%              Number of leaves         :   12 ( 441 expanded)
%              Depth                    :   14
%              Number of atoms          :  462 (8870 expanded)
%              Number of equality atoms :   11 ( 432 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   36 (   3 average)
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

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
               => ( r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))
                <=> r2_waybel_7(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_yellow19])).

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
    & ( ~ r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))
      | ~ r2_waybel_7(esk2_0,esk3_0,esk4_0) )
    & ( r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))
      | r2_waybel_7(esk2_0,esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_27,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_28,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_29,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r2_hidden(X27,k10_yellow_6(X25,X26))
        | r2_waybel_7(X25,k2_yellow19(X25,X26),X27)
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ r2_waybel_7(X25,k2_yellow19(X25,X26),X27)
        | r2_hidden(X27,k10_yellow_6(X25,X26))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | v2_struct_0(X26)
        | ~ v4_orders_2(X26)
        | ~ v7_waybel_0(X26)
        | ~ l1_waybel_0(X26,X25)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).

cnf(c_0_30,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))) ),
    inference(rw,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_38,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_41,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_44,plain,(
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

fof(c_0_45,plain,(
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

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))
    | r2_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( k2_yellow19(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_39]),c_0_37])])).

cnf(c_0_53,negated_conjecture,
    ( v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_39]),c_0_37])])).

cnf(c_0_54,negated_conjecture,
    ( v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_39]),c_0_37])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_36])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_58,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( r2_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_24]),c_0_49])]),c_0_36]),c_0_50])])).

cnf(c_0_61,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_35])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_18]),c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_64,negated_conjecture,
    ( v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_39]),c_0_37])])).

cnf(c_0_65,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( r2_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_39]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_37])]),c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_52]),c_0_64]),c_0_53]),c_0_54])]),c_0_55]),c_0_35])).

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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_31]),c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_72,negated_conjecture,
    ( r2_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_62]),c_0_37])]),c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0),X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_52]),c_0_53]),c_0_54])]),c_0_55]),c_0_35])).

cnf(c_0_75,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_39])).

cnf(c_0_77,negated_conjecture,
    ( r2_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])])).

cnf(c_0_78,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_62]),c_0_37])]),c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | r2_hidden(X1,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))
    | ~ r2_waybel_7(esk2_0,esk3_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_50]),c_0_48]),c_0_24])]),c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))
    | ~ r2_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_37])]),c_0_55])).

cnf(c_0_82,negated_conjecture,
    ( r2_waybel_7(esk2_0,esk3_0,esk4_0)
    | v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78])])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(X1,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)))
    | ~ r2_waybel_7(esk2_0,esk3_0,X1)
    | ~ l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_39]),c_0_73]),c_0_68]),c_0_37])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_waybel_7(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_39]),c_0_37])])).

cnf(c_0_85,negated_conjecture,
    ( r2_waybel_7(esk2_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_37]),c_0_62])]),c_0_36])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))
    | r2_hidden(X1,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)))
    | ~ r2_waybel_7(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_78])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_88,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_85]),c_0_49])]),c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_88]),c_0_37]),c_0_62])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:14:08 EST 2020
% 0.12/0.33  % CPUTime    : 
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
% 0.19/0.38  fof(t18_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow19)).
% 0.19/0.38  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.19/0.38  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.19/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(t13_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,X2))<=>r2_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow19)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.19/0.38  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.19/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k10_yellow_6(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))<=>r2_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t18_yellow19])).
% 0.19/0.38  fof(c_0_13, plain, ![X28, X29]:(v2_struct_0(X28)|~l1_struct_0(X28)|(v1_xboole_0(X29)|~v1_subset_1(X29,u1_struct_0(k3_yellow_1(k2_struct_0(X28))))|~v2_waybel_0(X29,k3_yellow_1(k2_struct_0(X28)))|~v13_waybel_0(X29,k3_yellow_1(k2_struct_0(X28)))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X28)))))|X29=k2_yellow19(X28,k3_yellow19(X28,k2_struct_0(X28),X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X15]:k3_yellow_1(X15)=k3_lattice3(k1_lattice3(X15)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((((~v1_xboole_0(esk3_0)&v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))&v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))))&v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0))))&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((~r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))|~r2_waybel_7(esk2_0,esk3_0,esk4_0))&(r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))|r2_waybel_7(esk2_0,esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.38  fof(c_0_16, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_17, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_18, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0)))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (v13_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (v2_waybel_0(esk3_0,k3_yellow_1(k2_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_23, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  fof(c_0_25, plain, ![X19, X20, X21]:((((~v2_struct_0(k3_yellow19(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20))))))&(v3_orders_2(k3_yellow19(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))))))&(v4_orders_2(k3_yellow19(X19,X20,X21))|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20)))))))&(v6_waybel_0(k3_yellow19(X19,X20,X21),X19)|(v2_struct_0(X19)|~l1_struct_0(X19)|v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|v1_xboole_0(X21)|~v2_waybel_0(X21,k3_yellow_1(X20))|~v13_waybel_0(X21,k3_yellow_1(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X20))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.19/0.38  fof(c_0_26, plain, ![X12]:(~l1_struct_0(X12)|k2_struct_0(X12)=u1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.38  fof(c_0_27, plain, ![X14]:(v2_struct_0(X14)|~l1_struct_0(X14)|~v1_xboole_0(u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.38  fof(c_0_28, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_29, plain, ![X25, X26, X27]:((~r2_hidden(X27,k10_yellow_6(X25,X26))|r2_waybel_7(X25,k2_yellow19(X25,X26),X27)|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~r2_waybel_7(X25,k2_yellow19(X25,X26),X27)|r2_hidden(X27,k10_yellow_6(X25,X26))|~m1_subset_1(X27,u1_struct_0(X25))|(v2_struct_0(X26)|~v4_orders_2(X26)|~v7_waybel_0(X26)|~l1_waybel_0(X26,X25))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow19])])])])])).
% 0.19/0.38  cnf(c_0_30, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk2_0)))))), inference(rw,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(k2_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_22, c_0_18])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  cnf(c_0_38, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_39, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  fof(c_0_41, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_43, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  fof(c_0_44, plain, ![X22, X23, X24]:(((~v2_struct_0(k3_yellow19(X22,X23,X24))|(v2_struct_0(X22)|~l1_struct_0(X22)|v1_xboole_0(X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v1_xboole_0(X24)|~v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))|~v2_waybel_0(X24,k3_yellow_1(X23))|~v13_waybel_0(X24,k3_yellow_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23))))))&(v6_waybel_0(k3_yellow19(X22,X23,X24),X22)|(v2_struct_0(X22)|~l1_struct_0(X22)|v1_xboole_0(X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v1_xboole_0(X24)|~v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))|~v2_waybel_0(X24,k3_yellow_1(X23))|~v13_waybel_0(X24,k3_yellow_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23)))))))&(v7_waybel_0(k3_yellow19(X22,X23,X24))|(v2_struct_0(X22)|~l1_struct_0(X22)|v1_xboole_0(X23)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|v1_xboole_0(X24)|~v1_subset_1(X24,u1_struct_0(k3_yellow_1(X23)))|~v2_waybel_0(X24,k3_yellow_1(X23))|~v13_waybel_0(X24,k3_yellow_1(X23))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X23))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.19/0.38  fof(c_0_45, plain, ![X16, X17, X18]:(((~v2_struct_0(k3_yellow19(X16,X17,X18))|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17))))))&(v6_waybel_0(k3_yellow19(X16,X17,X18),X16)|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17)))))))&(l1_waybel_0(k3_yellow19(X16,X17,X18),X16)|(v2_struct_0(X16)|~l1_struct_0(X16)|v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|v1_xboole_0(X18)|~v2_waybel_0(X18,k3_yellow_1(X17))|~v13_waybel_0(X18,k3_yellow_1(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X17))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.19/0.38  cnf(c_0_46, plain, (r2_waybel_7(X2,k2_yellow19(X2,X3),X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r2_hidden(X1,k10_yellow_6(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~v4_orders_2(X3)|~v7_waybel_0(X3)|~l1_waybel_0(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))|r2_waybel_7(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k2_yellow19(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])]), c_0_35]), c_0_36]), c_0_37])])).
% 0.19/0.38  cnf(c_0_51, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_39]), c_0_37])])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (v13_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_39]), c_0_37])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (v2_waybel_0(esk3_0,k3_lattice3(k1_lattice3(u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_39]), c_0_37])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_36])).
% 0.19/0.38  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.38  cnf(c_0_57, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  cnf(c_0_58, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.38  cnf(c_0_59, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (r2_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_24]), c_0_49])]), c_0_36]), c_0_50])])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (v4_orders_2(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54])]), c_0_55]), c_0_35])).
% 0.19/0.38  cnf(c_0_62, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.38  cnf(c_0_63, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_18]), c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (v1_subset_1(esk3_0,u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk2_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_39]), c_0_37])])).
% 0.19/0.38  cnf(c_0_65, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.38  cnf(c_0_66, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (r2_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_39]), c_0_37])])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (v4_orders_2(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_37])]), c_0_36])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_52]), c_0_64]), c_0_53]), c_0_54])]), c_0_55]), c_0_35])).
% 0.19/0.38  cnf(c_0_70, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_18]), c_0_18]), c_0_18])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (v1_xboole_0(k2_struct_0(esk2_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk2_0),esk3_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_31]), c_0_33]), c_0_34])]), c_0_35])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (r2_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.19/0.38  cnf(c_0_73, negated_conjecture, (v7_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_62]), c_0_37])]), c_0_36])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0),X1)|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_52]), c_0_53]), c_0_54])]), c_0_55]), c_0_35])).
% 0.19/0.38  cnf(c_0_75, plain, (r2_hidden(X3,k10_yellow_6(X1,X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_76, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|~l1_struct_0(esk2_0)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_71, c_0_39])).
% 0.19/0.38  cnf(c_0_77, negated_conjecture, (r2_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_62]), c_0_37])]), c_0_36])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|r2_hidden(X1,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))|~r2_waybel_7(esk2_0,esk3_0,X1)|~v7_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~v4_orders_2(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0))|~l1_waybel_0(k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0),esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_50]), c_0_48]), c_0_24])]), c_0_36])).
% 0.19/0.38  cnf(c_0_80, negated_conjecture, (~r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,k2_struct_0(esk2_0),esk3_0)))|~r2_waybel_7(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_81, negated_conjecture, (v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,u1_struct_0(esk2_0),esk3_0))|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_37])]), c_0_55])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (r2_waybel_7(esk2_0,esk3_0,esk4_0)|v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78])])).
% 0.19/0.38  cnf(c_0_83, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|r2_hidden(X1,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)))|~r2_waybel_7(esk2_0,esk3_0,X1)|~l1_waybel_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0),esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_39]), c_0_73]), c_0_68]), c_0_37])])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (~r2_waybel_7(esk2_0,esk3_0,esk4_0)|~r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_39]), c_0_37])])).
% 0.19/0.38  cnf(c_0_85, negated_conjecture, (r2_waybel_7(esk2_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_37]), c_0_62])]), c_0_36])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))|r2_hidden(X1,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)))|~r2_waybel_7(esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_78])])).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, (~r2_hidden(esk4_0,k10_yellow_6(esk2_0,k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 0.19/0.38  cnf(c_0_88, negated_conjecture, (v2_struct_0(k3_yellow19(esk2_0,u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_85]), c_0_49])]), c_0_87])).
% 0.19/0.38  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_88]), c_0_37]), c_0_62])]), c_0_36]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 90
% 0.19/0.38  # Proof object clause steps            : 65
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 47
% 0.19/0.38  # Proof object clause conjectures      : 44
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 25
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 25
% 0.19/0.38  # Proof object simplifying inferences  : 110
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 33
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 32
% 0.19/0.38  # Processed clauses                    : 121
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 27
% 0.19/0.38  # ...remaining for further processing  : 94
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 4
% 0.19/0.38  # Backward-rewritten                   : 15
% 0.19/0.38  # Generated clauses                    : 105
% 0.19/0.38  # ...of the previous two non-trivial   : 108
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 103
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
% 0.19/0.38  # Current number of processed clauses  : 75
% 0.19/0.38  #    Positive orientable unit clauses  : 25
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 45
% 0.19/0.38  # Current number of unprocessed clauses: 19
% 0.19/0.38  # ...number of literals in the above   : 84
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 20
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2441
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 273
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 26
% 0.19/0.38  # Unit Clause-clause subsumption calls : 119
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 26
% 0.19/0.38  # BW rewrite match successes           : 6
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8004
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.043 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.046 s
% 0.19/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
