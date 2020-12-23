%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:00 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  109 (1095 expanded)
%              Number of clauses        :   76 ( 454 expanded)
%              Number of leaves         :   16 ( 278 expanded)
%              Depth                    :   18
%              Number of atoms          :  601 (5632 expanded)
%              Number of equality atoms :   32 ( 498 expanded)
%              Maximal formula depth    :   17 (   6 average)
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

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

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

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ( ~ v1_tops_1(X16,X15)
        | k2_pre_topc(X15,X16) = u1_struct_0(X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( k2_pre_topc(X15,X16) != u1_struct_0(X15)
        | v1_tops_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).

fof(c_0_17,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | m1_subset_1(k2_struct_0(X6),k1_zfmisc_1(u1_struct_0(X6))) ) ),
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

cnf(c_0_19,plain,
    ( k2_pre_topc(X2,X1) = u1_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X10,X11] :
      ( ( ~ v4_pre_topc(X11,X10)
        | k2_pre_topc(X10,X11) = X11
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ v2_pre_topc(X10)
        | k2_pre_topc(X10,X11) != X11
        | v4_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

cnf(c_0_23,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | ~ v1_tops_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( v1_tops_1(k2_struct_0(X1),X1)
    | k2_pre_topc(X1,k2_struct_0(X1)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_25,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | k2_pre_topc(X1,k2_struct_0(X1)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = k2_struct_0(X1)
    | ~ v4_pre_topc(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_25,c_0_20])).

fof(c_0_28,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ l1_struct_0(X29)
      | v1_xboole_0(X30)
      | ~ v1_subset_1(X30,u1_struct_0(k3_yellow_1(k2_struct_0(X29))))
      | ~ v2_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))
      | ~ v13_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X29)))))
      | X30 = k2_yellow19(X29,k3_yellow19(X29,k2_struct_0(X29),X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_29,plain,(
    ! [X14] : k3_yellow_1(X14) = k3_lattice3(k1_lattice3(X14)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_30,negated_conjecture,(
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

cnf(c_0_31,plain,
    ( k2_pre_topc(X1,k2_struct_0(X1)) = u1_struct_0(X1)
    | ~ v4_pre_topc(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X9] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v4_pre_topc(k2_struct_0(X9),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

fof(c_0_33,plain,(
    ! [X26,X27,X28] :
      ( ( ~ r3_waybel_9(X26,X27,X28)
        | r1_waybel_7(X26,k2_yellow19(X26,X27),X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ r1_waybel_7(X26,k2_yellow19(X26,X27),X28)
        | r3_waybel_9(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | v2_struct_0(X27)
        | ~ v4_orders_2(X27)
        | ~ v7_waybel_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).

cnf(c_0_37,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ v4_pre_topc(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_38,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_struct_0(k3_yellow19(X17,X18,X19))
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17)
        | v1_xboole_0(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k3_yellow_1(X18))
        | ~ v13_waybel_0(X19,k3_yellow_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X18)))) )
      & ( v6_waybel_0(k3_yellow19(X17,X18,X19),X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17)
        | v1_xboole_0(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k3_yellow_1(X18))
        | ~ v13_waybel_0(X19,k3_yellow_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X18)))) )
      & ( l1_waybel_0(k3_yellow19(X17,X18,X19),X17)
        | v2_struct_0(X17)
        | ~ l1_struct_0(X17)
        | v1_xboole_0(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v1_xboole_0(X19)
        | ~ v2_waybel_0(X19,k3_yellow_1(X18))
        | ~ v13_waybel_0(X19,k3_yellow_1(X18))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X18)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_47,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1) ),
    inference(pm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_48,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_49,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v2_struct_0(k3_yellow19(X23,X24,X25))
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | v1_xboole_0(X25)
        | ~ v1_subset_1(X25,u1_struct_0(k3_yellow_1(X24)))
        | ~ v2_waybel_0(X25,k3_yellow_1(X24))
        | ~ v13_waybel_0(X25,k3_yellow_1(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X24)))) )
      & ( v6_waybel_0(k3_yellow19(X23,X24,X25),X23)
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | v1_xboole_0(X25)
        | ~ v1_subset_1(X25,u1_struct_0(k3_yellow_1(X24)))
        | ~ v2_waybel_0(X25,k3_yellow_1(X24))
        | ~ v13_waybel_0(X25,k3_yellow_1(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X24)))) )
      & ( v7_waybel_0(k3_yellow19(X23,X24,X25))
        | v2_struct_0(X23)
        | ~ l1_struct_0(X23)
        | v1_xboole_0(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | v1_xboole_0(X25)
        | ~ v1_subset_1(X25,u1_struct_0(k3_yellow_1(X24)))
        | ~ v2_waybel_0(X25,k3_yellow_1(X24))
        | ~ v13_waybel_0(X25,k3_yellow_1(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X24)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).

cnf(c_0_50,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( ~ r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ r1_waybel_7(X1,X2,X3)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_35])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

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
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_64,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_65,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_66,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_67,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v2_struct_0(k3_yellow19(X20,X21,X22))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v1_xboole_0(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v1_xboole_0(X22)
        | ~ v2_waybel_0(X22,k3_yellow_1(X21))
        | ~ v13_waybel_0(X22,k3_yellow_1(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21)))) )
      & ( v3_orders_2(k3_yellow19(X20,X21,X22))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v1_xboole_0(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v1_xboole_0(X22)
        | ~ v2_waybel_0(X22,k3_yellow_1(X21))
        | ~ v13_waybel_0(X22,k3_yellow_1(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21)))) )
      & ( v4_orders_2(k3_yellow19(X20,X21,X22))
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v1_xboole_0(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v1_xboole_0(X22)
        | ~ v2_waybel_0(X22,k3_yellow_1(X21))
        | ~ v13_waybel_0(X22,k3_yellow_1(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21)))) )
      & ( v6_waybel_0(k3_yellow19(X20,X21,X22),X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20)
        | v1_xboole_0(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | v1_xboole_0(X22)
        | ~ v2_waybel_0(X22,k3_yellow_1(X21))
        | ~ v13_waybel_0(X22,k3_yellow_1(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_68,plain,
    ( r1_waybel_7(X1,X2,X3)
    | v1_xboole_0(X2)
    | v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)
    | ~ v7_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v4_orders_2(k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)
    | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(pm,[status(thm)],[c_0_50,c_0_41])).

cnf(c_0_69,negated_conjecture,
    ( r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)
    | r1_waybel_7(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_70,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59])]),c_0_60]),c_0_61])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk1_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_63]),c_0_56]),c_0_57])])).

cnf(c_0_73,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54,c_0_63]),c_0_56]),c_0_57])])).

cnf(c_0_74,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_63]),c_0_56]),c_0_57])])).

cnf(c_0_75,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_76,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_77,plain,
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
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_78,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68,c_0_69]),c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58]),c_0_59])]),c_0_60]),c_0_61])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_63]),c_0_56]),c_0_57])])).

cnf(c_0_82,negated_conjecture,
    ( l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0),X1)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])]),c_0_60])).

cnf(c_0_83,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_58]),c_0_53]),c_0_54]),c_0_55])]),c_0_60])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v4_orders_2(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_86,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79,c_0_63]),c_0_56]),c_0_57])])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_82]),c_0_83])]),c_0_61])).

cnf(c_0_89,negated_conjecture,
    ( v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_84,c_0_20]),c_0_61])).

cnf(c_0_90,negated_conjecture,
    ( v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85,c_0_58]),c_0_54]),c_0_55])]),c_0_60])).

cnf(c_0_91,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_82]),c_0_83])]),c_0_61])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_87,c_0_58]),c_0_54]),c_0_55])]),c_0_60])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_90,c_0_20]),c_0_61])).

cnf(c_0_95,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_91,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | ~ v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_92,c_0_20]),c_0_61])).

cnf(c_0_97,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_95,c_0_94])).

fof(c_0_99,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | ~ v1_xboole_0(u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(k2_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_96,c_0_98])).

cnf(c_0_102,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100,c_0_63]),c_0_56]),c_0_57])])).

cnf(c_0_104,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_101,c_0_63]),c_0_56]),c_0_57])])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_102,c_0_103]),c_0_61])).

cnf(c_0_106,negated_conjecture,
    ( r1_waybel_7(esk1_0,esk2_0,esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_102,c_0_104]),c_0_61])).

cnf(c_0_107,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(pm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107,c_0_48]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:23:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.38/0.57  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.38/0.57  # and selection function NoSelection.
% 0.38/0.57  #
% 0.38/0.57  # Preprocessing time       : 0.029 s
% 0.38/0.57  
% 0.38/0.57  # Proof found!
% 0.38/0.57  # SZS status Theorem
% 0.38/0.57  # SZS output start CNFRefutation
% 0.38/0.57  fof(d2_tops_3, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_3)).
% 0.38/0.57  fof(dt_k2_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 0.38/0.57  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 0.38/0.57  fof(t52_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v4_pre_topc(X2,X1)=>k2_pre_topc(X1,X2)=X2)&((v2_pre_topc(X1)&k2_pre_topc(X1,X2)=X2)=>v4_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 0.38/0.57  fof(t15_yellow19, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 0.38/0.57  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.38/0.57  fof(t17_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_yellow19)).
% 0.38/0.57  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.38/0.57  fof(t12_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,X2,X3)<=>r1_waybel_7(X1,k2_yellow19(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_yellow19)).
% 0.38/0.57  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.38/0.57  fof(dt_k3_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&l1_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow19)).
% 0.38/0.57  fof(fc5_yellow19, axiom, ![X1, X2, X3]:(((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2))))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))&v7_waybel_0(k3_yellow19(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow19)).
% 0.38/0.57  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.38/0.57  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.38/0.57  fof(fc4_yellow19, axiom, ![X1, X2, X3]:((((((((~(v2_struct_0(X1))&l1_struct_0(X1))&~(v1_xboole_0(X2)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&~(v1_xboole_0(X3)))&v2_waybel_0(X3,k3_yellow_1(X2)))&v13_waybel_0(X3,k3_yellow_1(X2)))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))))=>(((~(v2_struct_0(k3_yellow19(X1,X2,X3)))&v3_orders_2(k3_yellow19(X1,X2,X3)))&v4_orders_2(k3_yellow19(X1,X2,X3)))&v6_waybel_0(k3_yellow19(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_yellow19)).
% 0.38/0.57  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.38/0.57  fof(c_0_16, plain, ![X15, X16]:((~v1_tops_1(X16,X15)|k2_pre_topc(X15,X16)=u1_struct_0(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))&(k2_pre_topc(X15,X16)!=u1_struct_0(X15)|v1_tops_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_3])])])])).
% 0.38/0.57  fof(c_0_17, plain, ![X6]:(~l1_struct_0(X6)|m1_subset_1(k2_struct_0(X6),k1_zfmisc_1(u1_struct_0(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).
% 0.38/0.57  fof(c_0_18, plain, ![X12, X13]:((~v1_tops_1(X13,X12)|k2_pre_topc(X12,X13)=k2_struct_0(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(k2_pre_topc(X12,X13)!=k2_struct_0(X12)|v1_tops_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.38/0.57  cnf(c_0_19, plain, (k2_pre_topc(X2,X1)=u1_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.38/0.57  cnf(c_0_20, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.38/0.57  cnf(c_0_21, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.57  fof(c_0_22, plain, ![X10, X11]:((~v4_pre_topc(X11,X10)|k2_pre_topc(X10,X11)=X11|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(~v2_pre_topc(X10)|k2_pre_topc(X10,X11)!=X11|v4_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).
% 0.38/0.57  cnf(c_0_23, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|~v1_tops_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_19, c_0_20])).
% 0.38/0.57  cnf(c_0_24, plain, (v1_tops_1(k2_struct_0(X1),X1)|k2_pre_topc(X1,k2_struct_0(X1))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_21, c_0_20])).
% 0.38/0.57  cnf(c_0_25, plain, (k2_pre_topc(X2,X1)=X1|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.57  cnf(c_0_26, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|k2_pre_topc(X1,k2_struct_0(X1))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_23, c_0_24])).
% 0.38/0.57  cnf(c_0_27, plain, (k2_pre_topc(X1,k2_struct_0(X1))=k2_struct_0(X1)|~v4_pre_topc(k2_struct_0(X1),X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_25, c_0_20])).
% 0.38/0.57  fof(c_0_28, plain, ![X29, X30]:(v2_struct_0(X29)|~l1_struct_0(X29)|(v1_xboole_0(X30)|~v1_subset_1(X30,u1_struct_0(k3_yellow_1(k2_struct_0(X29))))|~v2_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))|~v13_waybel_0(X30,k3_yellow_1(k2_struct_0(X29)))|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X29)))))|X30=k2_yellow19(X29,k3_yellow19(X29,k2_struct_0(X29),X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).
% 0.38/0.57  fof(c_0_29, plain, ![X14]:k3_yellow_1(X14)=k3_lattice3(k1_lattice3(X14)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.38/0.57  fof(c_0_30, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((((~(v1_xboole_0(X2))&v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))&v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1))))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)<=>r1_waybel_7(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t17_yellow19])).
% 0.38/0.57  cnf(c_0_31, plain, (k2_pre_topc(X1,k2_struct_0(X1))=u1_struct_0(X1)|~v4_pre_topc(k2_struct_0(X1),X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_26, c_0_27])).
% 0.38/0.57  fof(c_0_32, plain, ![X9]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|v4_pre_topc(k2_struct_0(X9),X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.38/0.57  fof(c_0_33, plain, ![X26, X27, X28]:((~r3_waybel_9(X26,X27,X28)|r1_waybel_7(X26,k2_yellow19(X26,X27),X28)|~m1_subset_1(X28,u1_struct_0(X26))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~r1_waybel_7(X26,k2_yellow19(X26,X27),X28)|r3_waybel_9(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|(v2_struct_0(X27)|~v4_orders_2(X27)|~v7_waybel_0(X27)|~l1_waybel_0(X27,X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).
% 0.38/0.57  cnf(c_0_34, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_struct_0(X1)|~v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.57  cnf(c_0_35, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.57  fof(c_0_36, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((((~v1_xboole_0(esk2_0)&v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))&v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0))))&m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&((~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0))&(r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_30])])])])).
% 0.38/0.57  cnf(c_0_37, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~v4_pre_topc(k2_struct_0(X1),X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_27, c_0_31])).
% 0.38/0.57  cnf(c_0_38, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.38/0.57  fof(c_0_39, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.38/0.57  cnf(c_0_40, plain, (r3_waybel_9(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.57  cnf(c_0_41, plain, (X2=k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.38/0.57  cnf(c_0_42, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_43, negated_conjecture, (v13_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_44, negated_conjecture, (v2_waybel_0(esk2_0,k3_yellow_1(k2_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk1_0)))))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  fof(c_0_46, plain, ![X17, X18, X19]:(((~v2_struct_0(k3_yellow19(X17,X18,X19))|(v2_struct_0(X17)|~l1_struct_0(X17)|v1_xboole_0(X18)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|v1_xboole_0(X19)|~v2_waybel_0(X19,k3_yellow_1(X18))|~v13_waybel_0(X19,k3_yellow_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X18))))))&(v6_waybel_0(k3_yellow19(X17,X18,X19),X17)|(v2_struct_0(X17)|~l1_struct_0(X17)|v1_xboole_0(X18)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|v1_xboole_0(X19)|~v2_waybel_0(X19,k3_yellow_1(X18))|~v13_waybel_0(X19,k3_yellow_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X18)))))))&(l1_waybel_0(k3_yellow19(X17,X18,X19),X17)|(v2_struct_0(X17)|~l1_struct_0(X17)|v1_xboole_0(X18)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|v1_xboole_0(X19)|~v2_waybel_0(X19,k3_yellow_1(X18))|~v13_waybel_0(X19,k3_yellow_1(X18))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X18))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).
% 0.38/0.57  cnf(c_0_47, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)), inference(pm,[status(thm)],[c_0_37, c_0_38])).
% 0.38/0.57  cnf(c_0_48, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.57  fof(c_0_49, plain, ![X23, X24, X25]:(((~v2_struct_0(k3_yellow19(X23,X24,X25))|(v2_struct_0(X23)|~l1_struct_0(X23)|v1_xboole_0(X24)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|v1_xboole_0(X25)|~v1_subset_1(X25,u1_struct_0(k3_yellow_1(X24)))|~v2_waybel_0(X25,k3_yellow_1(X24))|~v13_waybel_0(X25,k3_yellow_1(X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X24))))))&(v6_waybel_0(k3_yellow19(X23,X24,X25),X23)|(v2_struct_0(X23)|~l1_struct_0(X23)|v1_xboole_0(X24)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|v1_xboole_0(X25)|~v1_subset_1(X25,u1_struct_0(k3_yellow_1(X24)))|~v2_waybel_0(X25,k3_yellow_1(X24))|~v13_waybel_0(X25,k3_yellow_1(X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X24)))))))&(v7_waybel_0(k3_yellow19(X23,X24,X25))|(v2_struct_0(X23)|~l1_struct_0(X23)|v1_xboole_0(X24)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|v1_xboole_0(X25)|~v1_subset_1(X25,u1_struct_0(k3_yellow_1(X24)))|~v2_waybel_0(X25,k3_yellow_1(X24))|~v13_waybel_0(X25,k3_yellow_1(X24))|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X24))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_yellow19])])])])).
% 0.38/0.57  cnf(c_0_50, plain, (r1_waybel_7(X1,k2_yellow19(X1,X2),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r3_waybel_9(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~v4_orders_2(X2)|~v7_waybel_0(X2)|~l1_waybel_0(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.57  cnf(c_0_51, negated_conjecture, (~r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|~r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_52, plain, (r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)|v1_xboole_0(X2)|v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|~r1_waybel_7(X1,X2,X3)|~v7_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~v4_orders_2(k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))|~m1_subset_1(X3,u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_40, c_0_41])).
% 0.38/0.57  cnf(c_0_53, negated_conjecture, (v1_subset_1(esk2_0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0)))))), inference(rw,[status(thm)],[c_0_42, c_0_35])).
% 0.38/0.57  cnf(c_0_54, negated_conjecture, (v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_43, c_0_35])).
% 0.38/0.57  cnf(c_0_55, negated_conjecture, (v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))), inference(rw,[status(thm)],[c_0_44, c_0_35])).
% 0.38/0.57  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_57, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(esk1_0))))))), inference(rw,[status(thm)],[c_0_45, c_0_35])).
% 0.38/0.57  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_60, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_61, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_62, plain, (l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.57  cnf(c_0_63, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_47, c_0_48])).
% 0.38/0.57  fof(c_0_64, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.38/0.57  fof(c_0_65, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.38/0.57  cnf(c_0_66, plain, (v7_waybel_0(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_subset_1(X3,u1_struct_0(k3_yellow_1(X2)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.38/0.57  fof(c_0_67, plain, ![X20, X21, X22]:((((~v2_struct_0(k3_yellow19(X20,X21,X22))|(v2_struct_0(X20)|~l1_struct_0(X20)|v1_xboole_0(X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v1_xboole_0(X22)|~v2_waybel_0(X22,k3_yellow_1(X21))|~v13_waybel_0(X22,k3_yellow_1(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21))))))&(v3_orders_2(k3_yellow19(X20,X21,X22))|(v2_struct_0(X20)|~l1_struct_0(X20)|v1_xboole_0(X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v1_xboole_0(X22)|~v2_waybel_0(X22,k3_yellow_1(X21))|~v13_waybel_0(X22,k3_yellow_1(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21)))))))&(v4_orders_2(k3_yellow19(X20,X21,X22))|(v2_struct_0(X20)|~l1_struct_0(X20)|v1_xboole_0(X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v1_xboole_0(X22)|~v2_waybel_0(X22,k3_yellow_1(X21))|~v13_waybel_0(X22,k3_yellow_1(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21)))))))&(v6_waybel_0(k3_yellow19(X20,X21,X22),X20)|(v2_struct_0(X20)|~l1_struct_0(X20)|v1_xboole_0(X21)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|v1_xboole_0(X22)|~v2_waybel_0(X22,k3_yellow_1(X21))|~v13_waybel_0(X22,k3_yellow_1(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X21))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).
% 0.38/0.57  cnf(c_0_68, plain, (r1_waybel_7(X1,X2,X3)|v1_xboole_0(X2)|v2_struct_0(k3_yellow19(X1,k2_struct_0(X1),X2))|v2_struct_0(X1)|~r3_waybel_9(X1,k3_yellow19(X1,k2_struct_0(X1),X2),X3)|~v7_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2))|~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))|~v4_orders_2(k3_yellow19(X1,k2_struct_0(X1),X2))|~l1_waybel_0(k3_yellow19(X1,k2_struct_0(X1),X2),X1)|~v13_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v2_waybel_0(X2,k3_lattice3(k1_lattice3(k2_struct_0(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))|~m1_subset_1(X3,u1_struct_0(X1))), inference(pm,[status(thm)],[c_0_50, c_0_41])).
% 0.38/0.57  cnf(c_0_69, negated_conjecture, (r3_waybel_9(esk1_0,k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk3_0)|r1_waybel_7(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.38/0.57  cnf(c_0_70, negated_conjecture, (v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59])]), c_0_60]), c_0_61])).
% 0.38/0.57  cnf(c_0_71, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|l1_waybel_0(k3_yellow19(X1,X2,X3),X1)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_35]), c_0_35]), c_0_35])).
% 0.38/0.57  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(esk1_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_63]), c_0_56]), c_0_57])])).
% 0.38/0.57  cnf(c_0_73, negated_conjecture, (v13_waybel_0(esk2_0,k3_lattice3(k1_lattice3(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_54, c_0_63]), c_0_56]), c_0_57])])).
% 0.38/0.57  cnf(c_0_74, negated_conjecture, (v2_waybel_0(esk2_0,k3_lattice3(k1_lattice3(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_63]), c_0_56]), c_0_57])])).
% 0.38/0.57  cnf(c_0_75, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.38/0.57  cnf(c_0_76, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.38/0.57  cnf(c_0_77, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v7_waybel_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v1_subset_1(X3,u1_struct_0(k3_lattice3(k1_lattice3(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 0.38/0.57  cnf(c_0_78, plain, (v4_orders_2(k3_yellow19(X1,X2,X3))|v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.38/0.57  cnf(c_0_79, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68, c_0_69]), c_0_53]), c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58]), c_0_59])]), c_0_60]), c_0_61])).
% 0.38/0.57  cnf(c_0_80, plain, (v2_struct_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_yellow_1(X2))|~v13_waybel_0(X3,k3_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.57  cnf(c_0_81, negated_conjecture, (v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_63]), c_0_56]), c_0_57])])).
% 0.38/0.57  cnf(c_0_82, negated_conjecture, (l1_waybel_0(k3_yellow19(X1,u1_struct_0(esk1_0),esk2_0),X1)|v1_xboole_0(u1_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])]), c_0_60])).
% 0.38/0.57  cnf(c_0_83, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.38/0.57  cnf(c_0_84, negated_conjecture, (v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_58]), c_0_53]), c_0_54]), c_0_55])]), c_0_60])).
% 0.38/0.57  cnf(c_0_85, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|v4_orders_2(k3_yellow19(X1,X2,X3))|~l1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_35]), c_0_35]), c_0_35])).
% 0.38/0.57  cnf(c_0_86, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_waybel_0(k3_yellow19(esk1_0,u1_struct_0(esk1_0),esk2_0),esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79, c_0_63]), c_0_56]), c_0_57])])).
% 0.38/0.57  cnf(c_0_87, plain, (v2_struct_0(X1)|v1_xboole_0(X3)|v1_xboole_0(X2)|~l1_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~v13_waybel_0(X3,k3_lattice3(k1_lattice3(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_35]), c_0_35]), c_0_35])).
% 0.38/0.57  cnf(c_0_88, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_82]), c_0_83])]), c_0_61])).
% 0.38/0.57  cnf(c_0_89, negated_conjecture, (v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_84, c_0_20]), c_0_61])).
% 0.38/0.57  cnf(c_0_90, negated_conjecture, (v4_orders_2(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85, c_0_58]), c_0_54]), c_0_55])]), c_0_60])).
% 0.38/0.57  cnf(c_0_91, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v7_waybel_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_82]), c_0_83])]), c_0_61])).
% 0.38/0.57  cnf(c_0_92, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(X1)|~v2_struct_0(k3_yellow19(X1,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(X1)|~m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_87, c_0_58]), c_0_54]), c_0_55])]), c_0_60])).
% 0.38/0.57  cnf(c_0_93, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_88, c_0_89])).
% 0.38/0.57  cnf(c_0_94, negated_conjecture, (v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|v1_xboole_0(k2_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_90, c_0_20]), c_0_61])).
% 0.38/0.57  cnf(c_0_95, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk1_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~v4_orders_2(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_91, c_0_89])).
% 0.38/0.57  cnf(c_0_96, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|~v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_92, c_0_20]), c_0_61])).
% 0.38/0.57  cnf(c_0_97, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_93, c_0_94])).
% 0.38/0.57  cnf(c_0_98, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk1_0))|v1_xboole_0(k2_struct_0(esk1_0))|v2_struct_0(k3_yellow19(esk1_0,k2_struct_0(esk1_0),esk2_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_95, c_0_94])).
% 0.38/0.57  fof(c_0_99, plain, ![X8]:(v2_struct_0(X8)|~l1_struct_0(X8)|~v1_xboole_0(u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.38/0.57  cnf(c_0_100, negated_conjecture, (v1_xboole_0(k2_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk1_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_96, c_0_97])).
% 0.38/0.57  cnf(c_0_101, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(k2_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_96, c_0_98])).
% 0.38/0.57  cnf(c_0_102, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.38/0.57  cnf(c_0_103, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100, c_0_63]), c_0_56]), c_0_57])])).
% 0.38/0.57  cnf(c_0_104, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk1_0))|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_101, c_0_63]), c_0_56]), c_0_57])])).
% 0.38/0.57  cnf(c_0_105, negated_conjecture, (~r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_102, c_0_103]), c_0_61])).
% 0.38/0.57  cnf(c_0_106, negated_conjecture, (r1_waybel_7(esk1_0,esk2_0,esk3_0)|~l1_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_102, c_0_104]), c_0_61])).
% 0.38/0.57  cnf(c_0_107, negated_conjecture, (~l1_struct_0(esk1_0)), inference(pm,[status(thm)],[c_0_105, c_0_106])).
% 0.38/0.57  cnf(c_0_108, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107, c_0_48]), c_0_57])]), ['proof']).
% 0.38/0.57  # SZS output end CNFRefutation
% 0.38/0.57  # Proof object total steps             : 109
% 0.38/0.57  # Proof object clause steps            : 76
% 0.38/0.57  # Proof object formula steps           : 33
% 0.38/0.57  # Proof object conjectures             : 46
% 0.38/0.57  # Proof object clause conjectures      : 43
% 0.38/0.57  # Proof object formula conjectures     : 3
% 0.38/0.57  # Proof object initial clauses used    : 28
% 0.38/0.57  # Proof object initial formulas used   : 16
% 0.38/0.57  # Proof object generating inferences   : 38
% 0.38/0.57  # Proof object simplifying inferences  : 93
% 0.38/0.57  # Training examples: 0 positive, 0 negative
% 0.38/0.57  # Parsed axioms                        : 16
% 0.38/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.57  # Initial clauses                      : 37
% 0.38/0.57  # Removed in clause preprocessing      : 2
% 0.38/0.57  # Initial clauses in saturation        : 35
% 0.38/0.57  # Processed clauses                    : 2381
% 0.38/0.57  # ...of these trivial                  : 23
% 0.38/0.57  # ...subsumed                          : 1512
% 0.38/0.57  # ...remaining for further processing  : 846
% 0.38/0.57  # Other redundant clauses eliminated   : 0
% 0.38/0.57  # Clauses deleted for lack of memory   : 0
% 0.38/0.57  # Backward-subsumed                    : 60
% 0.38/0.57  # Backward-rewritten                   : 0
% 0.38/0.57  # Generated clauses                    : 8244
% 0.38/0.57  # ...of the previous two non-trivial   : 7741
% 0.38/0.57  # Contextual simplify-reflections      : 0
% 0.38/0.57  # Paramodulations                      : 8244
% 0.38/0.57  # Factorizations                       : 0
% 0.38/0.57  # Equation resolutions                 : 0
% 0.38/0.57  # Propositional unsat checks           : 0
% 0.38/0.57  #    Propositional check models        : 0
% 0.38/0.57  #    Propositional check unsatisfiable : 0
% 0.38/0.57  #    Propositional clauses             : 0
% 0.38/0.57  #    Propositional clauses after purity: 0
% 0.38/0.57  #    Propositional unsat core size     : 0
% 0.38/0.57  #    Propositional preprocessing time  : 0.000
% 0.38/0.57  #    Propositional encoding time       : 0.000
% 0.38/0.57  #    Propositional solver time         : 0.000
% 0.38/0.57  #    Success case prop preproc time    : 0.000
% 0.38/0.57  #    Success case prop encoding time   : 0.000
% 0.38/0.57  #    Success case prop solver time     : 0.000
% 0.38/0.57  # Current number of processed clauses  : 786
% 0.38/0.57  #    Positive orientable unit clauses  : 12
% 0.38/0.57  #    Positive unorientable unit clauses: 0
% 0.38/0.57  #    Negative unit clauses             : 3
% 0.38/0.57  #    Non-unit-clauses                  : 771
% 0.38/0.57  # Current number of unprocessed clauses: 5313
% 0.38/0.57  # ...number of literals in the above   : 38729
% 0.38/0.57  # Current number of archived formulas  : 0
% 0.38/0.57  # Current number of archived clauses   : 62
% 0.38/0.57  # Clause-clause subsumption calls (NU) : 84139
% 0.38/0.57  # Rec. Clause-clause subsumption calls : 2047
% 0.38/0.57  # Non-unit clause-clause subsumptions  : 1572
% 0.38/0.57  # Unit Clause-clause subsumption calls : 744
% 0.38/0.57  # Rewrite failures with RHS unbound    : 0
% 0.38/0.57  # BW rewrite match attempts            : 4
% 0.38/0.57  # BW rewrite match successes           : 0
% 0.38/0.57  # Condensation attempts                : 0
% 0.38/0.57  # Condensation successes               : 0
% 0.38/0.57  # Termbank termtop insertions          : 87832
% 0.38/0.57  
% 0.38/0.57  # -------------------------------------------------
% 0.38/0.57  # User time                : 0.231 s
% 0.38/0.57  # System time              : 0.010 s
% 0.38/0.57  # Total time               : 0.241 s
% 0.38/0.57  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
