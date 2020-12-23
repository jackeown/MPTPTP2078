%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2067+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:11 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  151 (24865 expanded)
%              Number of clauses        :  120 (8222 expanded)
%              Number of leaves         :   15 (6054 expanded)
%              Depth                    :   35
%              Number of atoms          :  947 (311427 expanded)
%              Number of equality atoms :   11 ( 468 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   54 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ? [X4] :
                    ( ~ v1_xboole_0(X4)
                    & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                    & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
                    & r2_hidden(X2,X4)
                    & r1_waybel_7(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow19)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t11_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_hidden(X3,k2_yellow19(X1,X2))
            <=> ( r1_waybel_0(X1,X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_yellow19)).

fof(t23_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ? [X4] :
                    ( ~ v2_struct_0(X4)
                    & v4_orders_2(X4)
                    & v7_waybel_0(X4)
                    & l1_waybel_0(X4,X1)
                    & r1_waybel_0(X1,X4,X2)
                    & r3_waybel_9(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow19)).

fof(fraenkel_a_2_1_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X2) )
     => ( r2_hidden(X1,a_2_1_yellow19(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = X4
            & r1_waybel_0(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_yellow19)).

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

fof(fc3_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ( v1_subset_1(k2_yellow19(X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
        & v2_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow19)).

fof(dt_k2_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => m1_subset_1(k2_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow19)).

fof(fc2_yellow19,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1) )
     => ( ~ v1_xboole_0(k2_yellow19(X1,X2))
        & v13_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow19)).

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

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

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

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_pre_topc(X1,X2))
                <=> ? [X4] :
                      ( ~ v1_xboole_0(X4)
                      & v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
                      & v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                      & v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X1)))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
                      & r2_hidden(X2,X4)
                      & r1_waybel_7(X1,X4,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_yellow19])).

fof(c_0_16,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_17,negated_conjecture,(
    ! [X50] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & ( ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
        | v1_xboole_0(X50)
        | ~ v1_subset_1(X50,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
        | ~ v2_waybel_0(X50,k3_yellow_1(k2_struct_0(esk3_0)))
        | ~ v13_waybel_0(X50,k3_yellow_1(k2_struct_0(esk3_0)))
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
        | ~ r2_hidden(esk4_0,X50)
        | ~ r1_waybel_7(esk3_0,X50,esk5_0) )
      & ( ~ v1_xboole_0(esk6_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk3_0)))
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk3_0)))
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( r2_hidden(esk4_0,esk6_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( r1_waybel_7(esk3_0,esk6_0,esk5_0)
        | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])])])).

fof(c_0_18,plain,(
    ! [X30,X31,X32] :
      ( ( r1_waybel_0(X30,X31,X32)
        | ~ r2_hidden(X32,k2_yellow19(X30,X31))
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30) )
      & ( m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(X32,k2_yellow19(X30,X31))
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30) )
      & ( ~ r1_waybel_0(X30,X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | r2_hidden(X32,k2_yellow19(X30,X31))
        | v2_struct_0(X31)
        | ~ l1_waybel_0(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_struct_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t11_yellow19])])])])])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X40,X41,X42,X44] :
      ( ( ~ v2_struct_0(esk2_3(X40,X41,X42))
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v4_orders_2(esk2_3(X40,X41,X42))
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v7_waybel_0(esk2_3(X40,X41,X42))
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( l1_waybel_0(esk2_3(X40,X41,X42),X40)
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r1_waybel_0(X40,esk2_3(X40,X41,X42),X41)
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( r3_waybel_9(X40,esk2_3(X40,X41,X42),X42)
        | ~ r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) )
      & ( v2_struct_0(X44)
        | ~ v4_orders_2(X44)
        | ~ v7_waybel_0(X44)
        | ~ l1_waybel_0(X44,X40)
        | ~ r1_waybel_0(X40,X44,X41)
        | ~ r3_waybel_9(X40,X44,X42)
        | r2_hidden(X42,k2_pre_topc(X40,X41))
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_yellow19])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,k2_yellow19(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_waybel_0(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r1_waybel_0(X1,esk2_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( l1_waybel_0(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk4_0,k2_yellow19(esk3_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk3_0,X1,esk4_0)
    | ~ l1_waybel_0(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk4_0,X1),esk4_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(esk2_3(esk3_0,esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_27]),c_0_20])]),c_0_25])).

fof(c_0_32,plain,(
    ! [X25,X26,X27,X29] :
      ( ( m1_subset_1(esk1_3(X25,X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | ~ r2_hidden(X25,a_2_1_yellow19(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26) )
      & ( X25 = esk1_3(X25,X26,X27)
        | ~ r2_hidden(X25,a_2_1_yellow19(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26) )
      & ( r1_waybel_0(X26,X27,esk1_3(X25,X26,X27))
        | ~ r2_hidden(X25,a_2_1_yellow19(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26) )
      & ( ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | X25 != X29
        | ~ r1_waybel_0(X26,X27,X29)
        | r2_hidden(X25,a_2_1_yellow19(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26)
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_yellow19])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,X1)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,a_2_1_yellow19(X2,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X1
    | ~ r1_waybel_0(X2,X4,X1)
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_yellow19(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_waybel_0(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_24])]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_1_yellow19(esk3_0,X1))
    | v2_struct_0(X1)
    | ~ r1_waybel_0(esk3_0,X1,esk4_0)
    | ~ l1_waybel_0(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),esk4_0)
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_31]),c_0_35])]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_1_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_1_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_31]),c_0_35])]),c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_24])]),c_0_25])).

cnf(c_0_47,plain,
    ( r1_waybel_0(X1,X2,esk1_3(X3,X1,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,a_2_1_yellow19(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_48,plain,(
    ! [X33,X34,X35] :
      ( ( ~ r3_waybel_9(X33,X34,X35)
        | r1_waybel_7(X33,k2_yellow19(X33,X34),X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r1_waybel_7(X33,k2_yellow19(X33,X34),X35)
        | r3_waybel_9(X33,X34,X35)
        | ~ m1_subset_1(X35,u1_struct_0(X33))
        | v2_struct_0(X34)
        | ~ v4_orders_2(X34)
        | ~ v7_waybel_0(X34)
        | ~ l1_waybel_0(X34,X33)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t12_yellow19])])])])])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X4,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ r1_waybel_0(X2,X1,X3)
    | ~ r3_waybel_9(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | m1_subset_1(esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_35])]),c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_24])]),c_0_25])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,plain,
    ( r3_waybel_9(X1,esk2_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0))))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk3_0,X2,X1)
    | ~ r1_waybel_0(esk3_0,X2,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_waybel_0(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( r1_waybel_0(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_31]),c_0_35])]),c_0_34])).

cnf(c_0_56,plain,
    ( v7_waybel_0(esk2_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,X1),esk5_0)
    | v2_struct_0(X1)
    | ~ r3_waybel_9(esk3_0,X1,esk5_0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_waybel_0(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( r3_waybel_9(esk3_0,esk2_3(esk3_0,esk4_0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0))))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r3_waybel_9(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),X1)
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( v7_waybel_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_23]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_61,plain,
    ( v4_orders_2(esk2_3(X1,X2,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_35])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0))))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r3_waybel_9(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),X1)
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_35])]),c_0_34])).

cnf(c_0_64,negated_conjecture,
    ( v4_orders_2(esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_23]),c_0_27]),c_0_20])]),c_0_25])).

fof(c_0_65,plain,(
    ! [X16,X17] :
      ( ( v1_subset_1(k2_yellow19(X16,X17),u1_struct_0(k3_yellow_1(k2_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v2_struct_0(X17)
        | ~ v4_orders_2(X17)
        | ~ v7_waybel_0(X17)
        | ~ l1_waybel_0(X17,X16) )
      & ( v2_waybel_0(k2_yellow19(X16,X17),k3_yellow_1(k2_struct_0(X16)))
        | v2_struct_0(X16)
        | ~ l1_struct_0(X16)
        | v2_struct_0(X17)
        | ~ v4_orders_2(X17)
        | ~ v7_waybel_0(X17)
        | ~ l1_waybel_0(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_yellow19])])])])).

fof(c_0_66,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v2_struct_0(X9)
      | ~ l1_waybel_0(X9,X8)
      | m1_subset_1(k2_yellow19(X8,X9),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X8))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_yellow19])])])).

fof(c_0_67,plain,(
    ! [X14,X15] :
      ( ( ~ v1_xboole_0(k2_yellow19(X14,X15))
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14) )
      & ( v13_waybel_0(k2_yellow19(X14,X15),k3_yellow_1(k2_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | v2_struct_0(X15)
        | ~ l1_waybel_0(X15,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_yellow19])])])])).

cnf(c_0_68,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_34])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0))))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r3_waybel_9(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_35])]),c_0_34])).

cnf(c_0_70,plain,
    ( v1_subset_1(k2_yellow19(X1,X2),u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(k2_yellow19(X1,X2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1)))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( v2_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( v13_waybel_0(k2_yellow19(X1,X2),k3_yellow_1(k2_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_60]),c_0_35])]),c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0))))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r3_waybel_9(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_31]),c_0_35])]),c_0_34])).

cnf(c_0_76,plain,
    ( X1 = esk1_3(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_2_1_yellow19(X2,X3))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_77,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | v1_xboole_0(X37)
      | ~ v1_subset_1(X37,u1_struct_0(k3_yellow_1(k2_struct_0(X36))))
      | ~ v2_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
      | ~ v13_waybel_0(X37,k3_yellow_1(k2_struct_0(X36)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X36)))))
      | X37 = k2_yellow19(X36,k3_yellow19(X36,k2_struct_0(X36),X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_yellow19])])])])).

fof(c_0_78,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_struct_0(k3_yellow19(X10,X11,X12))
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,k3_yellow_1(X11))
        | ~ v13_waybel_0(X12,k3_yellow_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11)))) )
      & ( v6_waybel_0(k3_yellow19(X10,X11,X12),X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,k3_yellow_1(X11))
        | ~ v13_waybel_0(X12,k3_yellow_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11)))) )
      & ( l1_waybel_0(k3_yellow19(X10,X11,X12),X10)
        | v2_struct_0(X10)
        | ~ l1_struct_0(X10)
        | v1_xboole_0(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | v1_xboole_0(X12)
        | ~ v2_waybel_0(X12,k3_yellow_1(X11))
        | ~ v13_waybel_0(X12,k3_yellow_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X11)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow19])])])])).

cnf(c_0_79,negated_conjecture,
    ( v1_subset_1(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,X1)),u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_31]),c_0_24])]),c_0_25]),c_0_64]),c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,X1)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_31]),c_0_24])]),c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( v2_waybel_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,X1)),k3_yellow_1(k2_struct_0(esk3_0)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_31]),c_0_24])]),c_0_25]),c_0_64]),c_0_60])).

cnf(c_0_82,negated_conjecture,
    ( v13_waybel_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,X1)),k3_yellow_1(k2_struct_0(esk3_0)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,X1))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_31]),c_0_24])]),c_0_25])).

cnf(c_0_83,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_64]),c_0_35])]),c_0_34])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | l1_waybel_0(esk2_3(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),X1),esk3_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_50]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0))))
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_58]),c_0_35])]),c_0_34])).

cnf(c_0_86,negated_conjecture,
    ( esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)) = esk4_0
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_45]),c_0_24])]),c_0_25])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | X2 = k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X2))
    | ~ l1_struct_0(X1)
    | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(k2_struct_0(X1))))
    | ~ v2_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X1))))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_89,negated_conjecture,
    ( v2_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk3_0)))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_90,negated_conjecture,
    ( v13_waybel_0(esk6_0,k3_yellow_1(k2_struct_0(esk3_0)))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_91,negated_conjecture,
    ( v1_subset_1(esk6_0,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_93,plain,
    ( l1_waybel_0(k3_yellow19(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

fof(c_0_94,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | m1_subset_1(k2_struct_0(X7),k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v2_struct_0(k3_yellow19(X1,X2,X3))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(esk3_0)))
    | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    | ~ r2_hidden(esk4_0,X1)
    | ~ r1_waybel_7(esk3_0,X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | v1_subset_1(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_34]),c_0_35])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | m1_subset_1(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_34]),c_0_35])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | v2_waybel_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k3_yellow_1(k2_struct_0(esk3_0)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_34]),c_0_35])])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | v13_waybel_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k3_yellow_1(k2_struct_0(esk3_0)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_34]),c_0_35])])).

cnf(c_0_101,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_31]),c_0_35])]),c_0_34])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | l1_waybel_0(esk2_3(esk3_0,esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0),esk3_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_35])])).

cnf(c_0_103,negated_conjecture,
    ( esk1_3(esk4_0,esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)) = esk4_0
    | r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_31]),c_0_35])]),c_0_34])).

fof(c_0_104,plain,(
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

fof(c_0_105,plain,(
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
      & ( v3_orders_2(k3_yellow19(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | v1_xboole_0(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | v1_xboole_0(X20)
        | ~ v2_waybel_0(X20,k3_yellow_1(X19))
        | ~ v13_waybel_0(X20,k3_yellow_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) )
      & ( v4_orders_2(k3_yellow19(X18,X19,X20))
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
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X19)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_yellow19])])])])).

cnf(c_0_106,negated_conjecture,
    ( k2_yellow19(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0)) = esk6_0
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_24])]),c_0_25]),c_0_89]),c_0_90]),c_0_91]),c_0_92])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | l1_waybel_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk6_0),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_88]),c_0_89]),c_0_90]),c_0_92])).

cnf(c_0_108,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk6_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_88]),c_0_89]),c_0_90]),c_0_92])).

cnf(c_0_110,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_xboole_0(k2_yellow19(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | v1_xboole_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99]),c_0_100]),c_0_34]),c_0_38]),c_0_101])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_113,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_114,plain,
    ( v4_orders_2(k3_yellow19(X1,X2,X3))
    | v2_struct_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(X3,k3_yellow_1(X2))
    | ~ v13_waybel_0(X3,k3_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_115,negated_conjecture,
    ( r1_waybel_0(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),X1)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_106]),c_0_24])]),c_0_25])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_24])]),c_0_25])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_108]),c_0_24])]),c_0_25])).

cnf(c_0_118,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(esk2_3(X1,X2,X3))
    | ~ r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0)
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_24])]),c_0_25]),c_0_112])).

cnf(c_0_120,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v7_waybel_0(k3_yellow19(X1,k2_struct_0(esk3_0),esk6_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_88]),c_0_89]),c_0_90]),c_0_91]),c_0_92])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v4_orders_2(k3_yellow19(X1,k2_struct_0(esk3_0),esk6_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_88]),c_0_89]),c_0_90]),c_0_92])).

cnf(c_0_123,negated_conjecture,
    ( r1_waybel_0(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),X1)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_27]),c_0_20]),c_0_23]),c_0_35])]),c_0_25]),c_0_34])).

cnf(c_0_125,negated_conjecture,
    ( r3_waybel_9(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),X1)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v2_struct_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0))
    | ~ r1_waybel_7(esk3_0,esk6_0,X1)
    | ~ v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0))
    | ~ v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_106]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_126,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v7_waybel_0(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0))
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_108]),c_0_24])]),c_0_25])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v4_orders_2(k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0))
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_108]),c_0_24])]),c_0_25])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | v2_struct_0(X2)
    | ~ r3_waybel_9(esk3_0,X2,X1)
    | ~ r1_waybel_0(esk3_0,X2,esk4_0)
    | ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ l1_waybel_0(X2,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_27]),c_0_20])]),c_0_25])).

cnf(c_0_129,negated_conjecture,
    ( r1_waybel_0(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),esk4_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_130,negated_conjecture,
    ( r3_waybel_9(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),X1)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ r1_waybel_7(esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_116]),c_0_127]),c_0_117])).

cnf(c_0_131,negated_conjecture,
    ( r1_waybel_7(esk3_0,esk6_0,esk5_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_132,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | ~ r3_waybel_9(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_116]),c_0_127]),c_0_126]),c_0_117])).

cnf(c_0_133,negated_conjecture,
    ( r3_waybel_9(esk3_0,k3_yellow19(esk3_0,k2_struct_0(esk3_0),esk6_0),esk5_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_131]),c_0_35])])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_35])])).

cnf(c_0_135,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v7_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_134])).

cnf(c_0_136,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ v4_orders_2(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_60]),c_0_35])]),c_0_134])).

cnf(c_0_137,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_64]),c_0_35])]),c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( v1_subset_1(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0))))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_134]),c_0_35])])).

cnf(c_0_139,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0))
    | m1_subset_1(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(esk3_0)))))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_134]),c_0_35])])).

cnf(c_0_140,negated_conjecture,
    ( v2_waybel_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k3_yellow_1(k2_struct_0(esk3_0)))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_134]),c_0_35])])).

cnf(c_0_141,negated_conjecture,
    ( v13_waybel_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),k3_yellow_1(k2_struct_0(esk3_0)))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_134]),c_0_35])])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(esk4_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_134]),c_0_35])])).

cnf(c_0_143,negated_conjecture,
    ( r1_waybel_7(esk3_0,k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk5_0)
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_31]),c_0_35])]),c_0_134])).

cnf(c_0_144,negated_conjecture,
    ( v1_xboole_0(k2_yellow19(esk3_0,esk2_3(esk3_0,esk4_0,esk5_0)))
    | v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_138]),c_0_139]),c_0_140]),c_0_141]),c_0_134]),c_0_142]),c_0_143])).

cnf(c_0_145,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0))
    | ~ l1_waybel_0(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_144]),c_0_24])]),c_0_25])).

fof(c_0_146,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_xboole_0(k2_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_147,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0))
    | v2_struct_0(esk2_3(esk3_0,esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_31]),c_0_35])]),c_0_134])).

cnf(c_0_148,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_146])).

cnf(c_0_149,negated_conjecture,
    ( v1_xboole_0(k2_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_147]),c_0_27]),c_0_20]),c_0_23]),c_0_35])]),c_0_25]),c_0_134])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_24])]),c_0_25]),
    [proof]).

%------------------------------------------------------------------------------
