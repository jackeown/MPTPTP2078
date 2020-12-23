%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:25 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_69)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( l1_waybel_0(X1,X0)
                & v7_waybel_0(X1)
                & v4_orders_2(X1)
                & ~ v2_struct_0(X1) )
             => ? [X2] :
                  ( v3_yellow_6(X2,X0)
                  & m2_yellow_6(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f66,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f67,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X1] :
            ( ? [X2] :
                ( v3_yellow_6(X2,X0)
                & m2_yellow_6(X2,X0,X1) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f68,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,X0)
                | ~ m2_yellow_6(X2,X0,X1) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(X0) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,X0)
                & m2_yellow_6(X4,X0,X3) )
            | ~ l1_waybel_0(X3,X0)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f67])).

fof(f71,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK10(X3),X0)
        & m2_yellow_6(sK10(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_yellow_6(X2,X0)
              | ~ m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ v3_yellow_6(X2,X0)
            | ~ m2_yellow_6(X2,X0,sK9) )
        & l1_waybel_0(sK9,X0)
        & v7_waybel_0(sK9)
        & v4_orders_2(sK9)
        & ~ v2_struct_0(sK9) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ! [X2] :
                  ( ~ v3_yellow_6(X2,X0)
                  | ~ m2_yellow_6(X2,X0,X1) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
          | ~ v1_compts_1(X0) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v3_yellow_6(X4,X0)
                  & m2_yellow_6(X4,X0,X3) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | v1_compts_1(X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_yellow_6(X2,sK8)
                | ~ m2_yellow_6(X2,sK8,X1) )
            & l1_waybel_0(X1,sK8)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK8) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK8)
                & m2_yellow_6(X4,sK8,X3) )
            | ~ l1_waybel_0(X3,sK8)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK8) )
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK8)
            | ~ m2_yellow_6(X2,sK8,sK9) )
        & l1_waybel_0(sK9,sK8)
        & v7_waybel_0(sK9)
        & v4_orders_2(sK9)
        & ~ v2_struct_0(sK9) )
      | ~ v1_compts_1(sK8) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK10(X3),sK8)
            & m2_yellow_6(sK10(X3),sK8,X3) )
          | ~ l1_waybel_0(X3,sK8)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK8) )
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f68,f71,f70,f69])).

fof(f112,plain,(
    ! [X3] :
      ( m2_yellow_6(sK10(X3),sK8,X3)
      | ~ l1_waybel_0(X3,sK8)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK8) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f109,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f111,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => r2_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> ! [X3] :
                    ( r2_waybel_0(X0,X1,X3)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( r2_waybel_0(X0,X1,X3)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ? [X3] :
                      ( ~ r2_waybel_0(X0,X1,X3)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
        & m1_connsp_2(sK4(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
                    & m1_connsp_2(sK4(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( r2_waybel_0(X0,X1,X4)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK4(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_waybel_9(X0,X1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X4)
      | ~ m1_connsp_2(X4,X0,X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_waybel_0(X0,X1,X3)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f61])).

fof(f64,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK7(X0,X3))
        & m1_subset_1(sK7(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK6(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK6(X0),X0)
        & v7_waybel_0(sK6(X0))
        & v4_orders_2(sK6(X0))
        & ~ v2_struct_0(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK6(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK6(X0),X0)
            & v7_waybel_0(sK6(X0))
            & v4_orders_2(sK6(X0))
            & ~ v2_struct_0(sK6(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK7(X0,X3))
                & m1_subset_1(sK7(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f62,f64,f63])).

fof(f108,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK6(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f105,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f106,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f107,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK6(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f103,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK7(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f114,plain,
    ( ~ v2_struct_0(sK9)
    | ~ v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f115,plain,
    ( v4_orders_2(sK9)
    | ~ v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f116,plain,
    ( v7_waybel_0(sK9)
    | ~ v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f117,plain,
    ( l1_waybel_0(sK9,sK8)
    | ~ v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f72])).

fof(f102,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK7(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
        & m2_yellow_6(sK5(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
                & m2_yellow_6(sK5(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f59])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK5(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k1_xboole_0 = k10_yellow_6(X0,X1) )
            & ( k1_xboole_0 != k10_yellow_6(X0,X1)
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k1_xboole_0 = k10_yellow_6(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f118,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK8)
      | ~ m2_yellow_6(X2,sK8,sK9)
      | ~ v1_compts_1(sK8) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f48])).

fof(f52,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
        & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
        & m1_connsp_2(sK2(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK1(X0,X1,X2)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK1(X0,X1,X2)) )
          | r2_hidden(sK1(X0,X1,X2),X2) )
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
                        & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2)) )
                      | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK1(X0,X1,X2)) )
                      | r2_hidden(sK1(X0,X1,X2),X2) )
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
                            & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK3(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f120,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK3(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f85,plain,(
    ! [X2,X0,X5,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r1_waybel_0(X0,X1,X5)
      | ~ m1_connsp_2(X5,X0,sK1(X0,X1,X2))
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f119,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_yellow_6(X0,X1)
      | ~ v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f113,plain,(
    ! [X3] :
      ( v3_yellow_6(sK10(X3),sK8)
      | ~ l1_waybel_0(X3,sK8)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK8) ) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8363,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_42,negated_conjecture,
    ( m2_yellow_6(sK10(X0),sK8,X0)
    | ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_8355,plain,
    ( m2_yellow_6(sK10(X0),sK8,X0) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | v1_compts_1(sK8) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_8365,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1527,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_44])).

cnf(c_1528,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1527])).

cnf(c_45,negated_conjecture,
    ( ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1532,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1528,c_45,c_43])).

cnf(c_1533,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1532])).

cnf(c_8337,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8361,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9847,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8337,c_8361])).

cnf(c_11611,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X1),u1_struct_0(sK8)) = iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8365,c_9847])).

cnf(c_24,plain,
    ( r3_waybel_9(X0,X1,X2)
    | m1_connsp_2(sK4(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1299,plain,
    ( r3_waybel_9(X0,X1,X2)
    | m1_connsp_2(sK4(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_44])).

cnf(c_1300,plain,
    ( r3_waybel_9(sK8,X0,X1)
    | m1_connsp_2(sK4(sK8,X0,X1),sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1299])).

cnf(c_1304,plain,
    ( r3_waybel_9(sK8,X0,X1)
    | m1_connsp_2(sK4(sK8,X0,X1),sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1300,c_45,c_43])).

cnf(c_8342,plain,
    ( r3_waybel_9(sK8,X0,X1) = iProver_top
    | m1_connsp_2(sK4(sK8,X0,X1),sK8,X1) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1304])).

cnf(c_26,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1236,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_44])).

cnf(c_1237,plain,
    ( r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1236])).

cnf(c_1241,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1237,c_45,c_43])).

cnf(c_1242,plain,
    ( r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1241])).

cnf(c_8344,plain,
    ( r3_waybel_9(sK8,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_9865,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(X1,u1_struct_0(sK8))
    | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9847])).

cnf(c_9973,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | r3_waybel_9(sK8,X0,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1242,c_9865])).

cnf(c_9974,plain,
    ( r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_9973])).

cnf(c_9975,plain,
    ( r3_waybel_9(sK8,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9974])).

cnf(c_10798,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | r3_waybel_9(sK8,X0,X1) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8344,c_9975])).

cnf(c_10799,plain,
    ( r3_waybel_9(sK8,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10798])).

cnf(c_10808,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X0),X1)) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8365,c_10799])).

cnf(c_25,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_waybel_0(X0,X1,X3)
    | ~ m1_connsp_2(X3,X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1269,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_waybel_0(X0,X1,X3)
    | ~ m1_connsp_2(X3,X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_44])).

cnf(c_1270,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_waybel_0(sK8,X0,X2)
    | ~ m1_connsp_2(X2,sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1269])).

cnf(c_1274,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | r2_waybel_0(sK8,X0,X2)
    | ~ m1_connsp_2(X2,sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1270,c_45,c_43])).

cnf(c_8343,plain,
    ( r3_waybel_9(sK8,X0,X1) != iProver_top
    | r2_waybel_0(sK8,X0,X2) = iProver_top
    | m1_connsp_2(X2,sK8,X1) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1274])).

cnf(c_11650,plain,
    ( r2_waybel_0(sK8,X0,X1) = iProver_top
    | m1_connsp_2(X1,sK8,sK0(k10_yellow_6(sK8,X0),X2)) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X2),u1_struct_0(sK8)) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10808,c_8343])).

cnf(c_13249,plain,
    ( r2_waybel_0(sK8,X0,X1) = iProver_top
    | m1_connsp_2(X1,sK8,sK0(k10_yellow_6(sK8,X0),X2)) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11650,c_11611])).

cnf(c_13253,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
    | r2_waybel_0(sK8,X1,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK8,X1),X2),u1_struct_0(sK8)) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8342,c_13249])).

cnf(c_14621,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
    | r2_waybel_0(sK8,X1,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13253,c_11611])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_20,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_591,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_7,c_20])).

cnf(c_1814,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_591,c_43])).

cnf(c_1815,plain,
    ( ~ r2_waybel_0(sK8,X0,X1)
    | r2_waybel_0(sK8,X2,X1)
    | ~ m2_yellow_6(X0,sK8,X2)
    | ~ l1_waybel_0(X2,sK8)
    | v2_struct_0(X2)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_1814])).

cnf(c_1817,plain,
    ( v2_struct_0(X2)
    | ~ l1_waybel_0(X2,sK8)
    | ~ m2_yellow_6(X0,sK8,X2)
    | r2_waybel_0(sK8,X2,X1)
    | ~ r2_waybel_0(sK8,X0,X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_45])).

cnf(c_1818,plain,
    ( ~ r2_waybel_0(sK8,X0,X1)
    | r2_waybel_0(sK8,X2,X1)
    | ~ m2_yellow_6(X0,sK8,X2)
    | ~ l1_waybel_0(X2,sK8)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1817])).

cnf(c_8331,plain,
    ( r2_waybel_0(sK8,X0,X1) != iProver_top
    | r2_waybel_0(sK8,X2,X1) = iProver_top
    | m2_yellow_6(X0,sK8,X2) != iProver_top
    | l1_waybel_0(X2,sK8) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_14624,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
    | r2_waybel_0(sK8,X3,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
    | m2_yellow_6(X1,sK8,X3) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | l1_waybel_0(X3,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X3) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14621,c_8331])).

cnf(c_17,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_677,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_678,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_1869,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_678,c_43])).

cnf(c_1870,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | v2_struct_0(X1)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1869])).

cnf(c_1872,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m2_yellow_6(X0,sK8,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1870,c_45])).

cnf(c_1873,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1872])).

cnf(c_8329,plain,
    ( m2_yellow_6(X0,sK8,X1) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1873])).

cnf(c_18,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_649,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_650,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_649])).

cnf(c_1895,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_650,c_43])).

cnf(c_1896,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | v2_struct_0(X1)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1895])).

cnf(c_1898,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m2_yellow_6(X0,sK8,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1896,c_45])).

cnf(c_1899,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1898])).

cnf(c_8328,plain,
    ( m2_yellow_6(X0,sK8,X1) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_19,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_621,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_622,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_1921,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_622,c_43])).

cnf(c_1922,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1921])).

cnf(c_1924,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m2_yellow_6(X0,sK8,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1922,c_45])).

cnf(c_1925,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1924])).

cnf(c_8327,plain,
    ( m2_yellow_6(X0,sK8,X1) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1925])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_705,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_706,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_1843,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_706,c_43])).

cnf(c_1844,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | l1_waybel_0(X0,sK8)
    | v2_struct_0(X1)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1843])).

cnf(c_1846,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m2_yellow_6(X0,sK8,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1844,c_45])).

cnf(c_1847,plain,
    ( ~ m2_yellow_6(X0,sK8,X1)
    | ~ l1_waybel_0(X1,sK8)
    | l1_waybel_0(X0,sK8)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1846])).

cnf(c_8330,plain,
    ( m2_yellow_6(X0,sK8,X1) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | l1_waybel_0(X0,sK8) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1847])).

cnf(c_16121,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
    | r2_waybel_0(sK8,X3,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
    | m2_yellow_6(X1,sK8,X3) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X3,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v4_orders_2(X3) != iProver_top
    | v7_waybel_0(X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14624,c_8329,c_8328,c_8327,c_8330])).

cnf(c_23,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1326,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_44])).

cnf(c_1327,plain,
    ( r3_waybel_9(sK8,X0,X1)
    | ~ r2_waybel_0(sK8,X0,sK4(sK8,X0,X1))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1326])).

cnf(c_1331,plain,
    ( r3_waybel_9(sK8,X0,X1)
    | ~ r2_waybel_0(sK8,X0,sK4(sK8,X0,X1))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_45,c_43])).

cnf(c_8341,plain,
    ( r3_waybel_9(sK8,X0,X1) = iProver_top
    | r2_waybel_0(sK8,X0,sK4(sK8,X0,X1)) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1331])).

cnf(c_16123,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK8,X0) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK8,X1),X2),u1_struct_0(sK8)) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16121,c_8341])).

cnf(c_16239,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK8,X0) != iProver_top
    | l1_waybel_0(X1,sK8) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11611,c_16123])).

cnf(c_18914,plain,
    ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
    | m2_yellow_6(X1,sK8,X0) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_16239,c_8329,c_8328,c_8327,c_8330])).

cnf(c_29,plain,
    ( ~ r3_waybel_9(X0,sK6(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1149,plain,
    ( ~ r3_waybel_9(X0,sK6(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_44])).

cnf(c_1150,plain,
    ( ~ r3_waybel_9(sK8,sK6(sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v1_compts_1(sK8)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1149])).

cnf(c_1154,plain,
    ( ~ r3_waybel_9(sK8,sK6(sK8),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK8))
    | v1_compts_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1150,c_45,c_43])).

cnf(c_8347,plain,
    ( r3_waybel_9(sK8,sK6(sK8),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
    | v1_compts_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1154])).

cnf(c_18916,plain,
    ( m2_yellow_6(X0,sK8,sK6(sK8)) != iProver_top
    | l1_waybel_0(sK6(sK8),sK8) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X1),u1_struct_0(sK8)) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
    | v1_compts_1(sK8) = iProver_top
    | v2_struct_0(sK6(sK8)) = iProver_top
    | v4_orders_2(sK6(sK8)) != iProver_top
    | v7_waybel_0(sK6(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18914,c_8347])).

cnf(c_33,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK6(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1093,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK6(X0))
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_44])).

cnf(c_1094,plain,
    ( v1_compts_1(sK8)
    | ~ v2_struct_0(sK6(sK8))
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1093])).

cnf(c_1096,plain,
    ( v1_compts_1(sK8)
    | ~ v2_struct_0(sK6(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1094,c_45,c_44,c_43,c_69])).

cnf(c_1098,plain,
    ( v1_compts_1(sK8) = iProver_top
    | v2_struct_0(sK6(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_32,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK6(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1107,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK6(X0))
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_44])).

cnf(c_1108,plain,
    ( v1_compts_1(sK8)
    | v2_struct_0(sK8)
    | v4_orders_2(sK6(sK8))
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1107])).

cnf(c_1110,plain,
    ( v4_orders_2(sK6(sK8))
    | v1_compts_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_45,c_43])).

cnf(c_1111,plain,
    ( v1_compts_1(sK8)
    | v4_orders_2(sK6(sK8)) ),
    inference(renaming,[status(thm)],[c_1110])).

cnf(c_1112,plain,
    ( v1_compts_1(sK8) = iProver_top
    | v4_orders_2(sK6(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1111])).

cnf(c_31,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK6(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1121,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK6(X0))
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_44])).

cnf(c_1122,plain,
    ( v1_compts_1(sK8)
    | v2_struct_0(sK8)
    | v7_waybel_0(sK6(sK8))
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1121])).

cnf(c_1124,plain,
    ( v7_waybel_0(sK6(sK8))
    | v1_compts_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1122,c_45,c_43])).

cnf(c_1125,plain,
    ( v1_compts_1(sK8)
    | v7_waybel_0(sK6(sK8)) ),
    inference(renaming,[status(thm)],[c_1124])).

cnf(c_1126,plain,
    ( v1_compts_1(sK8) = iProver_top
    | v7_waybel_0(sK6(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_30,plain,
    ( l1_waybel_0(sK6(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1135,plain,
    ( l1_waybel_0(sK6(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_44])).

cnf(c_1136,plain,
    ( l1_waybel_0(sK6(sK8),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(sK8)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1135])).

cnf(c_1138,plain,
    ( l1_waybel_0(sK6(sK8),sK8)
    | v1_compts_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1136,c_45,c_43])).

cnf(c_1140,plain,
    ( l1_waybel_0(sK6(sK8),sK8) = iProver_top
    | v1_compts_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_34,plain,
    ( r3_waybel_9(X0,X1,sK7(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1063,plain,
    ( r3_waybel_9(X0,X1,sK7(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_44])).

cnf(c_1064,plain,
    ( r3_waybel_9(sK8,X0,sK7(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v1_compts_1(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_1068,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK8,X0,sK7(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v1_compts_1(sK8)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_45,c_43])).

cnf(c_1069,plain,
    ( r3_waybel_9(sK8,X0,sK7(sK8,X0))
    | ~ l1_waybel_0(X0,sK8)
    | ~ v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1068])).

cnf(c_8352,plain,
    ( r3_waybel_9(sK8,X0,sK7(sK8,X0)) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | v1_compts_1(sK8) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_40,negated_conjecture,
    ( ~ v1_compts_1(sK8)
    | ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_55,plain,
    ( v1_compts_1(sK8) != iProver_top
    | v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( ~ v1_compts_1(sK8)
    | v4_orders_2(sK9) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_56,plain,
    ( v1_compts_1(sK8) != iProver_top
    | v4_orders_2(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( ~ v1_compts_1(sK8)
    | v7_waybel_0(sK9) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_57,plain,
    ( v1_compts_1(sK8) != iProver_top
    | v7_waybel_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_waybel_0(sK9,sK8)
    | ~ v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_58,plain,
    ( l1_waybel_0(sK9,sK8) = iProver_top
    | v1_compts_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK7(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1497,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK7(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_44])).

cnf(c_1498,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8))
    | ~ v1_compts_1(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1497])).

cnf(c_1502,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8))
    | ~ v1_compts_1(sK8)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1498,c_45,c_43])).

cnf(c_1503,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8))
    | ~ v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1502])).

cnf(c_8893,plain,
    ( ~ l1_waybel_0(sK9,sK8)
    | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8))
    | ~ v1_compts_1(sK8)
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_8894,plain,
    ( l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8)) = iProver_top
    | v1_compts_1(sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8893])).

cnf(c_8899,plain,
    ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9))
    | ~ l1_waybel_0(sK9,sK8)
    | ~ v1_compts_1(sK8)
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_8900,plain,
    ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9)) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v1_compts_1(sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8899])).

cnf(c_28,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK5(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1170,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK5(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_44])).

cnf(c_1171,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | m2_yellow_6(sK5(sK8,X0,X1),sK8,X0)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1170])).

cnf(c_1175,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,X1)
    | m2_yellow_6(sK5(sK8,X0,X1),sK8,X0)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1171,c_45,c_43])).

cnf(c_1176,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | m2_yellow_6(sK5(sK8,X0,X1),sK8,X0)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1175])).

cnf(c_9144,plain,
    ( ~ r3_waybel_9(sK8,sK9,sK7(sK8,sK9))
    | m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8))
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_9145,plain,
    ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9)) != iProver_top
    | m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9144])).

cnf(c_27,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1203,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_44])).

cnf(c_1204,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,k10_yellow_6(sK8,sK5(sK8,X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1203])).

cnf(c_1208,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,k10_yellow_6(sK8,sK5(sK8,X0,X1)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1204,c_45,c_43])).

cnf(c_1209,plain,
    ( ~ r3_waybel_9(sK8,X0,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,k10_yellow_6(sK8,sK5(sK8,X0,X1)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1208])).

cnf(c_9143,plain,
    ( ~ r3_waybel_9(sK8,sK9,sK7(sK8,sK9))
    | ~ l1_waybel_0(sK9,sK8)
    | ~ m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8))
    | r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))))
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1209])).

cnf(c_9147,plain,
    ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9)) != iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9)))) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9143])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9297,plain,
    ( ~ r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))))
    | ~ r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9298,plain,
    ( r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9)))) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9297])).

cnf(c_21,plain,
    ( v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_36,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK8,sK9)
    | ~ v3_yellow_6(X0,sK8)
    | ~ v1_compts_1(sK8) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_780,plain,
    ( ~ m2_yellow_6(X0,sK8,sK9)
    | ~ l1_waybel_0(X1,X2)
    | ~ v1_compts_1(sK8)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k10_yellow_6(X2,X1) = k1_xboole_0
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_781,plain,
    ( ~ m2_yellow_6(X0,sK8,sK9)
    | ~ l1_waybel_0(X0,sK8)
    | ~ v1_compts_1(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8)
    | k10_yellow_6(sK8,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_780])).

cnf(c_785,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m2_yellow_6(X0,sK8,sK9)
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_781,c_45,c_44,c_43])).

cnf(c_786,plain,
    ( ~ m2_yellow_6(X0,sK8,sK9)
    | ~ l1_waybel_0(X0,sK8)
    | ~ v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK8,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_785])).

cnf(c_9326,plain,
    ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
    | ~ l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8)
    | ~ v1_compts_1(sK8)
    | v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9)))
    | ~ v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9)))
    | ~ v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)))
    | k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_9327,plain,
    ( k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) = k1_xboole_0
    | m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
    | l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8) != iProver_top
    | v1_compts_1(sK8) != iProver_top
    | v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9))) = iProver_top
    | v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9))) != iProver_top
    | v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9326])).

cnf(c_9336,plain,
    ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
    | l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8)
    | ~ l1_waybel_0(sK9,sK8)
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_9337,plain,
    ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
    | l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8) = iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9336])).

cnf(c_9335,plain,
    ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
    | ~ l1_waybel_0(sK9,sK8)
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK9)
    | v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)))
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1873])).

cnf(c_9339,plain,
    ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9))) = iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9335])).

cnf(c_9334,plain,
    ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
    | ~ l1_waybel_0(sK9,sK8)
    | v2_struct_0(sK9)
    | v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9)))
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_9341,plain,
    ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9))) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9334])).

cnf(c_9557,plain,
    ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,X0)
    | ~ l1_waybel_0(X0,sK8)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9)))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_9725,plain,
    ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
    | ~ l1_waybel_0(sK9,sK8)
    | ~ v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9)))
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK9)
    | ~ v7_waybel_0(sK9) ),
    inference(instantiation,[status(thm)],[c_9557])).

cnf(c_9726,plain,
    ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
    | l1_waybel_0(sK9,sK8) != iProver_top
    | v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9))) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK9) != iProver_top
    | v7_waybel_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9725])).

cnf(c_7459,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_9732,plain,
    ( ~ r1_tarski(X0,sK7(sK8,sK9))
    | r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9))
    | k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) != X0 ),
    inference(instantiation,[status(thm)],[c_7459])).

cnf(c_10390,plain,
    ( r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9))
    | ~ r1_tarski(k1_xboole_0,sK7(sK8,sK9))
    | k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9732])).

cnf(c_10392,plain,
    ( k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) != k1_xboole_0
    | r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9)) = iProver_top
    | r1_tarski(k1_xboole_0,sK7(sK8,sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10390])).

cnf(c_10391,plain,
    ( r1_tarski(k1_xboole_0,sK7(sK8,sK9)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10394,plain,
    ( r1_tarski(k1_xboole_0,sK7(sK8,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10391])).

cnf(c_10405,plain,
    ( v1_compts_1(sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8352,c_55,c_56,c_57,c_58,c_8894,c_8900,c_9145,c_9147,c_9298,c_9327,c_9337,c_9339,c_9341,c_9726,c_10392,c_10394])).

cnf(c_19144,plain,
    ( m2_yellow_6(X0,sK8,sK6(sK8)) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X1),u1_struct_0(sK8)) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18916,c_55,c_56,c_57,c_58,c_1098,c_1112,c_1126,c_1140,c_8894,c_8900,c_9145,c_9147,c_9298,c_9327,c_9337,c_9339,c_9341,c_9726,c_10392,c_10394])).

cnf(c_19153,plain,
    ( m2_yellow_6(X0,sK8,sK6(sK8)) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11611,c_19144])).

cnf(c_20211,plain,
    ( l1_waybel_0(sK10(sK6(sK8)),sK8) != iProver_top
    | l1_waybel_0(sK6(sK8),sK8) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,sK10(sK6(sK8))),X0) = iProver_top
    | v1_compts_1(sK8) = iProver_top
    | v2_struct_0(sK10(sK6(sK8))) = iProver_top
    | v2_struct_0(sK6(sK8)) = iProver_top
    | v4_orders_2(sK10(sK6(sK8))) != iProver_top
    | v4_orders_2(sK6(sK8)) != iProver_top
    | v7_waybel_0(sK10(sK6(sK8))) != iProver_top
    | v7_waybel_0(sK6(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8355,c_19153])).

cnf(c_8348,plain,
    ( l1_waybel_0(sK6(sK8),sK8) = iProver_top
    | v1_compts_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1138])).

cnf(c_9161,plain,
    ( l1_waybel_0(X0,sK8) != iProver_top
    | v1_compts_1(sK8) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK10(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8355,c_8327])).

cnf(c_9487,plain,
    ( v1_compts_1(sK8) = iProver_top
    | v2_struct_0(sK10(sK6(sK8))) != iProver_top
    | v2_struct_0(sK6(sK8)) = iProver_top
    | v4_orders_2(sK6(sK8)) != iProver_top
    | v7_waybel_0(sK6(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8348,c_9161])).

cnf(c_9014,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK10(X0)) ),
    inference(resolution,[status(thm)],[c_1873,c_42])).

cnf(c_9030,plain,
    ( v1_compts_1(sK8)
    | v2_struct_0(sK6(sK8))
    | ~ v4_orders_2(sK6(sK8))
    | v7_waybel_0(sK10(sK6(sK8)))
    | ~ v7_waybel_0(sK6(sK8)) ),
    inference(resolution,[status(thm)],[c_9014,c_1138])).

cnf(c_72,plain,
    ( v1_compts_1(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8)
    | v4_orders_2(sK6(sK8))
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_75,plain,
    ( v1_compts_1(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(sK8)
    | v7_waybel_0(sK6(sK8))
    | ~ l1_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_10243,plain,
    ( v7_waybel_0(sK10(sK6(sK8)))
    | v1_compts_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9030,c_45,c_44,c_43,c_72,c_75,c_1094])).

cnf(c_10244,plain,
    ( v1_compts_1(sK8)
    | v7_waybel_0(sK10(sK6(sK8))) ),
    inference(renaming,[status(thm)],[c_10243])).

cnf(c_10245,plain,
    ( v1_compts_1(sK8) = iProver_top
    | v7_waybel_0(sK10(sK6(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10244])).

cnf(c_9098,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK10(X0))
    | ~ v7_waybel_0(X0) ),
    inference(resolution,[status(thm)],[c_1899,c_42])).

cnf(c_9177,plain,
    ( v1_compts_1(sK8)
    | v2_struct_0(sK6(sK8))
    | v4_orders_2(sK10(sK6(sK8)))
    | ~ v4_orders_2(sK6(sK8))
    | ~ v7_waybel_0(sK6(sK8)) ),
    inference(resolution,[status(thm)],[c_9098,c_1138])).

cnf(c_10304,plain,
    ( v1_compts_1(sK8)
    | v4_orders_2(sK10(sK6(sK8))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9177,c_45,c_44,c_43,c_69,c_72,c_75])).

cnf(c_10306,plain,
    ( v1_compts_1(sK8) = iProver_top
    | v4_orders_2(sK10(sK6(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10304])).

cnf(c_10889,plain,
    ( m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8))
    | ~ l1_waybel_0(sK6(sK8),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(sK6(sK8))
    | ~ v4_orders_2(sK6(sK8))
    | ~ v7_waybel_0(sK6(sK8)) ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_10919,plain,
    ( m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8)) = iProver_top
    | l1_waybel_0(sK6(sK8),sK8) != iProver_top
    | v1_compts_1(sK8) = iProver_top
    | v2_struct_0(sK6(sK8)) = iProver_top
    | v4_orders_2(sK6(sK8)) != iProver_top
    | v7_waybel_0(sK6(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10889])).

cnf(c_12425,plain,
    ( ~ m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8))
    | l1_waybel_0(sK10(sK6(sK8)),sK8)
    | ~ l1_waybel_0(sK6(sK8),sK8)
    | v2_struct_0(sK6(sK8))
    | ~ v4_orders_2(sK6(sK8))
    | ~ v7_waybel_0(sK6(sK8)) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_12426,plain,
    ( m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8)) != iProver_top
    | l1_waybel_0(sK10(sK6(sK8)),sK8) = iProver_top
    | l1_waybel_0(sK6(sK8),sK8) != iProver_top
    | v2_struct_0(sK6(sK8)) = iProver_top
    | v4_orders_2(sK6(sK8)) != iProver_top
    | v7_waybel_0(sK6(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12425])).

cnf(c_20348,plain,
    ( r1_tarski(k10_yellow_6(sK8,sK10(sK6(sK8))),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20211,c_55,c_56,c_57,c_58,c_1098,c_1112,c_1126,c_1140,c_8894,c_8900,c_9145,c_9147,c_9298,c_9327,c_9337,c_9339,c_9341,c_9487,c_9726,c_10245,c_10306,c_10392,c_10394,c_10919,c_12426])).

cnf(c_13,plain,
    ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1353,plain,
    ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_44])).

cnf(c_1354,plain,
    ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1353])).

cnf(c_1358,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1354,c_45,c_43])).

cnf(c_1359,plain,
    ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1358])).

cnf(c_1550,plain,
    ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1533,c_1359])).

cnf(c_8336,plain,
    ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1550])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,sK1(X1,X2,X3))
    | r1_waybel_0(X1,X2,X0)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK1(X1,X2,X3),X3)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1635,plain,
    ( ~ m1_connsp_2(X0,X1,sK1(X1,X2,X3))
    | r1_waybel_0(X1,X2,X0)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(sK1(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X2) = X3
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_44])).

cnf(c_1636,plain,
    ( ~ m1_connsp_2(X0,sK8,sK1(sK8,X1,X2))
    | r1_waybel_0(sK8,X1,X0)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK1(sK8,X1,X2),X2)
    | v2_struct_0(X1)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(sK8)
    | k10_yellow_6(sK8,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_1635])).

cnf(c_1640,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_connsp_2(X0,sK8,sK1(sK8,X1,X2))
    | r1_waybel_0(sK8,X1,X0)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK1(sK8,X1,X2),X2)
    | v2_struct_0(X1)
    | k10_yellow_6(sK8,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1636,c_45,c_43])).

cnf(c_1641,plain,
    ( ~ m1_connsp_2(X0,sK8,sK1(sK8,X1,X2))
    | r1_waybel_0(sK8,X1,X0)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK1(sK8,X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | k10_yellow_6(sK8,X1) = X2 ),
    inference(renaming,[status(thm)],[c_1640])).

cnf(c_8332,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | m1_connsp_2(X2,sK8,sK1(sK8,X0,X1)) != iProver_top
    | r1_waybel_0(sK8,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1641])).

cnf(c_12773,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
    | l1_waybel_0(X2,sK8) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8336,c_8332])).

cnf(c_2378,plain,
    ( r1_waybel_0(sK8,X0,X1)
    | ~ l1_waybel_0(X2,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X3,u1_struct_0(sK8))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X3,k10_yellow_6(sK8,X2))
    | r2_hidden(sK1(sK8,X0,X4),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X0)
    | sK3(sK8,X2,X3) != X1
    | sK1(sK8,X0,X4) != X3
    | k10_yellow_6(sK8,X0) = X4
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_1550,c_1641])).

cnf(c_2379,plain,
    ( r1_waybel_0(sK8,X0,sK3(sK8,X1,sK1(sK8,X0,X2)))
    | ~ l1_waybel_0(X1,sK8)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK1(sK8,X0,X2),u1_struct_0(sK8))
    | r2_hidden(sK1(sK8,X0,X2),X2)
    | r2_hidden(sK1(sK8,X0,X2),k10_yellow_6(sK8,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK8,X0) = X2 ),
    inference(unflattening,[status(thm)],[c_2378])).

cnf(c_11,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1602,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_44])).

cnf(c_1603,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8)
    | k10_yellow_6(sK8,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1602])).

cnf(c_1607,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8))
    | v2_struct_0(X0)
    | k10_yellow_6(sK8,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1603,c_45,c_43])).

cnf(c_1608,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK8,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1607])).

cnf(c_2411,plain,
    ( r1_waybel_0(sK8,X0,sK3(sK8,X1,sK1(sK8,X0,X2)))
    | ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(sK1(sK8,X0,X2),X2)
    | r2_hidden(sK1(sK8,X0,X2),k10_yellow_6(sK8,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK8,X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2379,c_1608])).

cnf(c_2425,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X2,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2411])).

cnf(c_16351,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X2,sK8) != iProver_top
    | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
    | k10_yellow_6(sK8,X0) = X1
    | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12773,c_2425])).

cnf(c_16352,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X2,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_16351])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8364,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_16368,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | l1_waybel_0(X2,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X3) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_16352,c_8364])).

cnf(c_12,plain,
    ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1389,plain,
    ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_44])).

cnf(c_1390,plain,
    ( ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_1389])).

cnf(c_1394,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1390,c_45,c_43])).

cnf(c_1395,plain,
    ( ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1394])).

cnf(c_1551,plain,
    ( ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
    | ~ l1_waybel_0(X0,sK8)
    | ~ m1_subset_1(X1,u1_struct_0(sK8))
    | r2_hidden(X1,k10_yellow_6(sK8,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1533,c_1395])).

cnf(c_8335,plain,
    ( r1_waybel_0(sK8,X0,sK3(sK8,X0,X1)) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK8,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1551])).

cnf(c_17045,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8)) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X0)) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16368,c_8335])).

cnf(c_1609,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1608])).

cnf(c_22044,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | l1_waybel_0(X0,sK8) != iProver_top
    | k10_yellow_6(sK8,X0) = X1
    | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X0)) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17045,c_1609])).

cnf(c_22045,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
    | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X0)) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_22044])).

cnf(c_8360,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_22060,plain,
    ( k10_yellow_6(sK8,X0) = X1
    | l1_waybel_0(X0,sK8) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k10_yellow_6(sK8,X0),sK1(sK8,X0,X1)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22045,c_8360])).

cnf(c_22332,plain,
    ( k10_yellow_6(sK8,sK10(sK6(sK8))) = X0
    | l1_waybel_0(sK10(sK6(sK8)),sK8) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v2_struct_0(sK10(sK6(sK8))) = iProver_top
    | v4_orders_2(sK10(sK6(sK8))) != iProver_top
    | v7_waybel_0(sK10(sK6(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20348,c_22060])).

cnf(c_23897,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | k10_yellow_6(sK8,sK10(sK6(sK8))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22332,c_55,c_56,c_57,c_58,c_1098,c_1112,c_1126,c_1140,c_8894,c_8900,c_9145,c_9147,c_9298,c_9327,c_9337,c_9339,c_9341,c_9487,c_9726,c_10245,c_10306,c_10392,c_10394,c_10919,c_12426])).

cnf(c_23898,plain,
    ( k10_yellow_6(sK8,sK10(sK6(sK8))) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_23897])).

cnf(c_23907,plain,
    ( k10_yellow_6(sK8,sK10(sK6(sK8))) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_23898,c_8364])).

cnf(c_24587,plain,
    ( k10_yellow_6(sK8,sK10(sK6(sK8))) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
    | r2_hidden(sK1(sK8,sK10(sK6(sK8)),k1_xboole_0),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8363,c_23907])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8926,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8928,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8926])).

cnf(c_10407,plain,
    ( ~ v1_compts_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10405])).

cnf(c_2695,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | l1_waybel_0(X2,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X0 != X1
    | sK10(X1) != X2
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_1847])).

cnf(c_2696,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | l1_waybel_0(sK10(X0),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2695])).

cnf(c_2671,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X2)
    | X0 != X1
    | sK10(X1) != X2
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_1873])).

cnf(c_2672,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK10(X0)) ),
    inference(unflattening,[status(thm)],[c_2671])).

cnf(c_2647,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X0 != X1
    | sK10(X1) != X2
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_1899])).

cnf(c_2648,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK10(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2647])).

cnf(c_2623,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(X1,sK8)
    | v1_compts_1(sK8)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X0 != X1
    | sK10(X1) != X2
    | sK8 != sK8 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_1925])).

cnf(c_2624,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK10(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2623])).

cnf(c_22,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,negated_conjecture,
    ( v3_yellow_6(sK10(X0),sK8)
    | ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_813,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK8)
    | v1_compts_1(sK8)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0
    | sK10(X2) != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_41])).

cnf(c_814,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(sK10(X0),sK8)
    | v1_compts_1(sK8)
    | ~ v2_pre_topc(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK10(X0))
    | v2_struct_0(sK8)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK10(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK10(X0))
    | ~ l1_pre_topc(sK8)
    | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_818,plain,
    ( ~ v7_waybel_0(sK10(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(sK10(X0))
    | ~ v4_orders_2(X0)
    | v1_compts_1(sK8)
    | ~ l1_waybel_0(sK10(X0),sK8)
    | ~ l1_waybel_0(X0,sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK10(X0))
    | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_814,c_45,c_44,c_43])).

cnf(c_819,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(sK10(X0),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | v2_struct_0(sK10(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK10(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK10(X0))
    | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_818])).

cnf(c_2876,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(sK10(X0),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK10(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK10(X0))
    | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2624,c_819])).

cnf(c_2887,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(sK10(X0),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK10(X0))
    | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2648,c_2876])).

cnf(c_2898,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | ~ l1_waybel_0(sK10(X0),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2672,c_2887])).

cnf(c_2904,plain,
    ( ~ l1_waybel_0(X0,sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2696,c_2898])).

cnf(c_16733,plain,
    ( ~ l1_waybel_0(sK6(sK8),sK8)
    | v1_compts_1(sK8)
    | v2_struct_0(sK6(sK8))
    | ~ v4_orders_2(sK6(sK8))
    | ~ v7_waybel_0(sK6(sK8))
    | k10_yellow_6(sK8,sK10(sK6(sK8))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2904])).

cnf(c_24831,plain,
    ( r2_hidden(sK1(sK8,sK10(sK6(sK8)),k1_xboole_0),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24587,c_45,c_44,c_43,c_69,c_72,c_75,c_78,c_8928,c_10407,c_16733])).

cnf(c_24839,plain,
    ( r2_hidden(sK1(sK8,sK10(sK6(sK8)),k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8363,c_24831])).

cnf(c_8362,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9846,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8362,c_8361])).

cnf(c_571,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_572,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_573,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_10576,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9846,c_573])).

cnf(c_24857,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_24839,c_10576])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:58:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.67/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.67/1.49  
% 7.67/1.49  ------  iProver source info
% 7.67/1.49  
% 7.67/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.67/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.67/1.49  git: non_committed_changes: false
% 7.67/1.49  git: last_make_outside_of_git: false
% 7.67/1.49  
% 7.67/1.49  ------ 
% 7.67/1.49  ------ Parsing...
% 7.67/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.67/1.49  
% 7.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.67/1.49  ------ Proving...
% 7.67/1.49  ------ Problem Properties 
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  clauses                                 41
% 7.67/1.49  conjectures                             6
% 7.67/1.49  EPR                                     13
% 7.67/1.49  Horn                                    14
% 7.67/1.49  unary                                   3
% 7.67/1.49  binary                                  11
% 7.67/1.49  lits                                    192
% 7.67/1.49  lits eq                                 6
% 7.67/1.49  fd_pure                                 0
% 7.67/1.49  fd_pseudo                               0
% 7.67/1.49  fd_cond                                 0
% 7.67/1.49  fd_pseudo_cond                          4
% 7.67/1.49  AC symbols                              0
% 7.67/1.49  
% 7.67/1.49  ------ Input Options Time Limit: Unbounded
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ 
% 7.67/1.49  Current options:
% 7.67/1.49  ------ 
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  ------ Proving...
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  % SZS status Theorem for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49   Resolution empty clause
% 7.67/1.49  
% 7.67/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  fof(f2,axiom,(
% 7.67/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f76,plain,(
% 7.67/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f2])).
% 7.67/1.49  
% 7.67/1.49  fof(f16,conjecture,(
% 7.67/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f17,negated_conjecture,(
% 7.67/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 7.67/1.49    inference(negated_conjecture,[],[f16])).
% 7.67/1.49  
% 7.67/1.49  fof(f41,plain,(
% 7.67/1.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f17])).
% 7.67/1.49  
% 7.67/1.49  fof(f42,plain,(
% 7.67/1.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f41])).
% 7.67/1.49  
% 7.67/1.49  fof(f66,plain,(
% 7.67/1.49    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.67/1.49    inference(nnf_transformation,[],[f42])).
% 7.67/1.49  
% 7.67/1.49  fof(f67,plain,(
% 7.67/1.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f66])).
% 7.67/1.49  
% 7.67/1.49  fof(f68,plain,(
% 7.67/1.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.67/1.49    inference(rectify,[],[f67])).
% 7.67/1.49  
% 7.67/1.49  fof(f71,plain,(
% 7.67/1.49    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK10(X3),X0) & m2_yellow_6(sK10(X3),X0,X3)))) )),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f70,plain,(
% 7.67/1.49    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK9)) & l1_waybel_0(sK9,X0) & v7_waybel_0(sK9) & v4_orders_2(sK9) & ~v2_struct_0(sK9))) )),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f69,plain,(
% 7.67/1.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK8) | ~m2_yellow_6(X2,sK8,X1)) & l1_waybel_0(X1,sK8) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK8)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK8) & m2_yellow_6(X4,sK8,X3)) | ~l1_waybel_0(X3,sK8) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK8)) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f72,plain,(
% 7.67/1.49    ((! [X2] : (~v3_yellow_6(X2,sK8) | ~m2_yellow_6(X2,sK8,sK9)) & l1_waybel_0(sK9,sK8) & v7_waybel_0(sK9) & v4_orders_2(sK9) & ~v2_struct_0(sK9)) | ~v1_compts_1(sK8)) & (! [X3] : ((v3_yellow_6(sK10(X3),sK8) & m2_yellow_6(sK10(X3),sK8,X3)) | ~l1_waybel_0(X3,sK8) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK8)) & l1_pre_topc(sK8) & v2_pre_topc(sK8) & ~v2_struct_0(sK8)),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f68,f71,f70,f69])).
% 7.67/1.49  
% 7.67/1.49  fof(f112,plain,(
% 7.67/1.49    ( ! [X3] : (m2_yellow_6(sK10(X3),sK8,X3) | ~l1_waybel_0(X3,sK8) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK8)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f1,axiom,(
% 7.67/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f18,plain,(
% 7.67/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f1])).
% 7.67/1.49  
% 7.67/1.49  fof(f43,plain,(
% 7.67/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.67/1.49    inference(nnf_transformation,[],[f18])).
% 7.67/1.49  
% 7.67/1.49  fof(f44,plain,(
% 7.67/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.67/1.49    inference(rectify,[],[f43])).
% 7.67/1.49  
% 7.67/1.49  fof(f45,plain,(
% 7.67/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f46,plain,(
% 7.67/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 7.67/1.49  
% 7.67/1.49  fof(f74,plain,(
% 7.67/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f46])).
% 7.67/1.49  
% 7.67/1.49  fof(f8,axiom,(
% 7.67/1.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f25,plain,(
% 7.67/1.49    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f8])).
% 7.67/1.49  
% 7.67/1.49  fof(f26,plain,(
% 7.67/1.49    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f25])).
% 7.67/1.49  
% 7.67/1.49  fof(f88,plain,(
% 7.67/1.49    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f26])).
% 7.67/1.49  
% 7.67/1.49  fof(f110,plain,(
% 7.67/1.49    v2_pre_topc(sK8)),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f109,plain,(
% 7.67/1.49    ~v2_struct_0(sK8)),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f111,plain,(
% 7.67/1.49    l1_pre_topc(sK8)),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f4,axiom,(
% 7.67/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f19,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.67/1.49    inference(ennf_transformation,[],[f4])).
% 7.67/1.49  
% 7.67/1.49  fof(f20,plain,(
% 7.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.67/1.49    inference(flattening,[],[f19])).
% 7.67/1.49  
% 7.67/1.49  fof(f78,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f20])).
% 7.67/1.49  
% 7.67/1.49  fof(f12,axiom,(
% 7.67/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => r2_waybel_0(X0,X1,X3))))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f33,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f12])).
% 7.67/1.49  
% 7.67/1.49  fof(f34,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f33])).
% 7.67/1.49  
% 7.67/1.49  fof(f55,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(nnf_transformation,[],[f34])).
% 7.67/1.49  
% 7.67/1.49  fof(f56,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(rectify,[],[f55])).
% 7.67/1.49  
% 7.67/1.49  fof(f57,plain,(
% 7.67/1.49    ! [X2,X1,X0] : (? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2)) => (~r2_waybel_0(X0,X1,sK4(X0,X1,X2)) & m1_connsp_2(sK4(X0,X1,X2),X0,X2)))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f58,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | (~r2_waybel_0(X0,X1,sK4(X0,X1,X2)) & m1_connsp_2(sK4(X0,X1,X2),X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f56,f57])).
% 7.67/1.49  
% 7.67/1.49  fof(f97,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | m1_connsp_2(sK4(X0,X1,X2),X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f58])).
% 7.67/1.49  
% 7.67/1.49  fof(f13,axiom,(
% 7.67/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f35,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f13])).
% 7.67/1.49  
% 7.67/1.49  fof(f36,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f35])).
% 7.67/1.49  
% 7.67/1.49  fof(f99,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f36])).
% 7.67/1.49  
% 7.67/1.49  fof(f96,plain,(
% 7.67/1.49    ( ! [X4,X2,X0,X1] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f58])).
% 7.67/1.49  
% 7.67/1.49  fof(f6,axiom,(
% 7.67/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f22,plain,(
% 7.67/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.67/1.49    inference(ennf_transformation,[],[f6])).
% 7.67/1.49  
% 7.67/1.49  fof(f80,plain,(
% 7.67/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f22])).
% 7.67/1.49  
% 7.67/1.49  fof(f10,axiom,(
% 7.67/1.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f29,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f10])).
% 7.67/1.49  
% 7.67/1.49  fof(f30,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f29])).
% 7.67/1.49  
% 7.67/1.49  fof(f93,plain,(
% 7.67/1.49    ( ! [X2,X0,X3,X1] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f30])).
% 7.67/1.49  
% 7.67/1.49  fof(f9,axiom,(
% 7.67/1.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f27,plain,(
% 7.67/1.49    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f9])).
% 7.67/1.49  
% 7.67/1.49  fof(f28,plain,(
% 7.67/1.49    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f27])).
% 7.67/1.49  
% 7.67/1.49  fof(f91,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f28])).
% 7.67/1.49  
% 7.67/1.49  fof(f90,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f28])).
% 7.67/1.49  
% 7.67/1.49  fof(f89,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f28])).
% 7.67/1.49  
% 7.67/1.49  fof(f92,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f28])).
% 7.67/1.49  
% 7.67/1.49  fof(f98,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_waybel_0(X0,X1,sK4(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f58])).
% 7.67/1.49  
% 7.67/1.49  fof(f15,axiom,(
% 7.67/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f39,plain,(
% 7.67/1.49    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f15])).
% 7.67/1.49  
% 7.67/1.49  fof(f40,plain,(
% 7.67/1.49    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f39])).
% 7.67/1.49  
% 7.67/1.49  fof(f61,plain,(
% 7.67/1.49    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(nnf_transformation,[],[f40])).
% 7.67/1.49  
% 7.67/1.49  fof(f62,plain,(
% 7.67/1.49    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(rectify,[],[f61])).
% 7.67/1.49  
% 7.67/1.49  fof(f64,plain,(
% 7.67/1.49    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK7(X0,X3)) & m1_subset_1(sK7(X0,X3),u1_struct_0(X0))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f63,plain,(
% 7.67/1.49    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK6(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK6(X0),X0) & v7_waybel_0(sK6(X0)) & v4_orders_2(sK6(X0)) & ~v2_struct_0(sK6(X0))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f65,plain,(
% 7.67/1.49    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK6(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK6(X0),X0) & v7_waybel_0(sK6(X0)) & v4_orders_2(sK6(X0)) & ~v2_struct_0(sK6(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK7(X0,X3)) & m1_subset_1(sK7(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f62,f64,f63])).
% 7.67/1.49  
% 7.67/1.49  fof(f108,plain,(
% 7.67/1.49    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK6(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f65])).
% 7.67/1.49  
% 7.67/1.49  fof(f104,plain,(
% 7.67/1.49    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK6(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f65])).
% 7.67/1.49  
% 7.67/1.49  fof(f105,plain,(
% 7.67/1.49    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK6(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f65])).
% 7.67/1.49  
% 7.67/1.49  fof(f106,plain,(
% 7.67/1.49    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK6(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f65])).
% 7.67/1.49  
% 7.67/1.49  fof(f107,plain,(
% 7.67/1.49    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK6(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f65])).
% 7.67/1.49  
% 7.67/1.49  fof(f103,plain,(
% 7.67/1.49    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK7(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f65])).
% 7.67/1.49  
% 7.67/1.49  fof(f114,plain,(
% 7.67/1.49    ~v2_struct_0(sK9) | ~v1_compts_1(sK8)),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f115,plain,(
% 7.67/1.49    v4_orders_2(sK9) | ~v1_compts_1(sK8)),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f116,plain,(
% 7.67/1.49    v7_waybel_0(sK9) | ~v1_compts_1(sK8)),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f117,plain,(
% 7.67/1.49    l1_waybel_0(sK9,sK8) | ~v1_compts_1(sK8)),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f102,plain,(
% 7.67/1.49    ( ! [X0,X3] : (m1_subset_1(sK7(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f65])).
% 7.67/1.49  
% 7.67/1.49  fof(f14,axiom,(
% 7.67/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f37,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f14])).
% 7.67/1.49  
% 7.67/1.49  fof(f38,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f37])).
% 7.67/1.49  
% 7.67/1.49  fof(f59,plain,(
% 7.67/1.49    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f60,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) & m2_yellow_6(sK5(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f59])).
% 7.67/1.49  
% 7.67/1.49  fof(f100,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (m2_yellow_6(sK5(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f60])).
% 7.67/1.49  
% 7.67/1.49  fof(f101,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f60])).
% 7.67/1.49  
% 7.67/1.49  fof(f5,axiom,(
% 7.67/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f21,plain,(
% 7.67/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.67/1.49    inference(ennf_transformation,[],[f5])).
% 7.67/1.49  
% 7.67/1.49  fof(f79,plain,(
% 7.67/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f21])).
% 7.67/1.49  
% 7.67/1.49  fof(f11,axiom,(
% 7.67/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f31,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f11])).
% 7.67/1.49  
% 7.67/1.49  fof(f32,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f31])).
% 7.67/1.49  
% 7.67/1.49  fof(f54,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(nnf_transformation,[],[f32])).
% 7.67/1.49  
% 7.67/1.49  fof(f95,plain,(
% 7.67/1.49    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f54])).
% 7.67/1.49  
% 7.67/1.49  fof(f118,plain,(
% 7.67/1.49    ( ! [X2] : (~v3_yellow_6(X2,sK8) | ~m2_yellow_6(X2,sK8,sK9) | ~v1_compts_1(sK8)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  fof(f7,axiom,(
% 7.67/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f23,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.67/1.49    inference(ennf_transformation,[],[f7])).
% 7.67/1.49  
% 7.67/1.49  fof(f24,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f23])).
% 7.67/1.49  
% 7.67/1.49  fof(f47,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(nnf_transformation,[],[f24])).
% 7.67/1.49  
% 7.67/1.49  fof(f48,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(flattening,[],[f47])).
% 7.67/1.49  
% 7.67/1.49  fof(f49,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(rectify,[],[f48])).
% 7.67/1.49  
% 7.67/1.49  fof(f52,plain,(
% 7.67/1.49    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6)))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f51,plain,(
% 7.67/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,X3)))) )),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f50,plain,(
% 7.67/1.49    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 7.67/1.49    introduced(choice_axiom,[])).
% 7.67/1.49  
% 7.67/1.49  fof(f53,plain,(
% 7.67/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).
% 7.67/1.49  
% 7.67/1.49  fof(f82,plain,(
% 7.67/1.49    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK3(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f53])).
% 7.67/1.49  
% 7.67/1.49  fof(f120,plain,(
% 7.67/1.49    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK3(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(equality_resolution,[],[f82])).
% 7.67/1.49  
% 7.67/1.49  fof(f85,plain,(
% 7.67/1.49    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2)) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f53])).
% 7.67/1.49  
% 7.67/1.49  fof(f84,plain,(
% 7.67/1.49    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f53])).
% 7.67/1.49  
% 7.67/1.49  fof(f73,plain,(
% 7.67/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f46])).
% 7.67/1.49  
% 7.67/1.49  fof(f83,plain,(
% 7.67/1.49    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f53])).
% 7.67/1.49  
% 7.67/1.49  fof(f119,plain,(
% 7.67/1.49    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(equality_resolution,[],[f83])).
% 7.67/1.49  
% 7.67/1.49  fof(f3,axiom,(
% 7.67/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.67/1.49  
% 7.67/1.49  fof(f77,plain,(
% 7.67/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.67/1.49    inference(cnf_transformation,[],[f3])).
% 7.67/1.49  
% 7.67/1.49  fof(f94,plain,(
% 7.67/1.49    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f54])).
% 7.67/1.49  
% 7.67/1.49  fof(f113,plain,(
% 7.67/1.49    ( ! [X3] : (v3_yellow_6(sK10(X3),sK8) | ~l1_waybel_0(X3,sK8) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK8)) )),
% 7.67/1.49    inference(cnf_transformation,[],[f72])).
% 7.67/1.49  
% 7.67/1.49  cnf(c_3,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8363,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_42,negated_conjecture,
% 7.67/1.49      ( m2_yellow_6(sK10(X0),sK8,X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8355,plain,
% 7.67/1.49      ( m2_yellow_6(sK10(X0),sK8,X0) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1,plain,
% 7.67/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8365,plain,
% 7.67/1.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.67/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_15,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.67/1.49      | ~ v2_pre_topc(X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_44,negated_conjecture,
% 7.67/1.49      ( v2_pre_topc(sK8) ),
% 7.67/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1527,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1528,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1527]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_45,negated_conjecture,
% 7.67/1.49      ( ~ v2_struct_0(sK8) ),
% 7.67/1.49      inference(cnf_transformation,[],[f109]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_43,negated_conjecture,
% 7.67/1.49      ( l1_pre_topc(sK8) ),
% 7.67/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1532,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1528,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1533,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1532]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8337,plain,
% 7.67/1.49      ( l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1533]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_5,plain,
% 7.67/1.49      ( m1_subset_1(X0,X1)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.67/1.49      | ~ r2_hidden(X0,X2) ),
% 7.67/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8361,plain,
% 7.67/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.67/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.67/1.49      | r2_hidden(X0,X2) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9847,plain,
% 7.67/1.49      ( l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8)) = iProver_top
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8337,c_8361]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_11611,plain,
% 7.67/1.49      ( l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X1),u1_struct_0(sK8)) = iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8365,c_9847]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | m1_connsp_2(sK4(X0,X1,X2),X0,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1299,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | m1_connsp_2(sK4(X0,X1,X2),X0,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1300,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | m1_connsp_2(sK4(sK8,X0,X1),sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1299]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1304,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | m1_connsp_2(sK4(sK8,X0,X1),sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1300,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8342,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1) = iProver_top
% 7.67/1.49      | m1_connsp_2(sK4(sK8,X0,X1),sK8,X1) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1304]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_26,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1236,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1237,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1236]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1241,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1237,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1242,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1241]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8344,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9865,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_9847]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9973,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1242,c_9865]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9974,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_9973]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9975,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9974]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10798,plain,
% 7.67/1.49      ( l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r3_waybel_9(sK8,X0,X1) = iProver_top
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_8344,c_9975]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10799,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_10798]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10808,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X0),X1)) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8365,c_10799]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_25,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | r2_waybel_0(X0,X1,X3)
% 7.67/1.49      | ~ m1_connsp_2(X3,X0,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1269,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | r2_waybel_0(X0,X1,X3)
% 7.67/1.49      | ~ m1_connsp_2(X3,X0,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1270,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | r2_waybel_0(sK8,X0,X2)
% 7.67/1.49      | ~ m1_connsp_2(X2,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1269]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1274,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | r2_waybel_0(sK8,X0,X2)
% 7.67/1.49      | ~ m1_connsp_2(X2,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1270,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8343,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1) != iProver_top
% 7.67/1.49      | r2_waybel_0(sK8,X0,X2) = iProver_top
% 7.67/1.49      | m1_connsp_2(X2,sK8,X1) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1274]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_11650,plain,
% 7.67/1.49      ( r2_waybel_0(sK8,X0,X1) = iProver_top
% 7.67/1.49      | m1_connsp_2(X1,sK8,sK0(k10_yellow_6(sK8,X0),X2)) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X2),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_10808,c_8343]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_13249,plain,
% 7.67/1.49      ( r2_waybel_0(sK8,X0,X1) = iProver_top
% 7.67/1.49      | m1_connsp_2(X1,sK8,sK0(k10_yellow_6(sK8,X0),X2)) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_11650,c_11611]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_13253,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
% 7.67/1.49      | r2_waybel_0(sK8,X1,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK0(k10_yellow_6(sK8,X1),X2),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8342,c_13249]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_14621,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
% 7.67/1.49      | r2_waybel_0(sK8,X1,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top ),
% 7.67/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_13253,c_11611]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_7,plain,
% 7.67/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_20,plain,
% 7.67/1.49      ( ~ r2_waybel_0(X0,X1,X2)
% 7.67/1.49      | r2_waybel_0(X0,X3,X2)
% 7.67/1.49      | ~ m2_yellow_6(X1,X0,X3)
% 7.67/1.49      | ~ l1_waybel_0(X3,X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X3)
% 7.67/1.49      | ~ v4_orders_2(X3)
% 7.67/1.49      | ~ v7_waybel_0(X3)
% 7.67/1.49      | ~ l1_struct_0(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_591,plain,
% 7.67/1.49      ( ~ r2_waybel_0(X0,X1,X2)
% 7.67/1.49      | r2_waybel_0(X0,X3,X2)
% 7.67/1.49      | ~ m2_yellow_6(X1,X0,X3)
% 7.67/1.49      | ~ l1_waybel_0(X3,X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X3)
% 7.67/1.49      | ~ v4_orders_2(X3)
% 7.67/1.49      | ~ v7_waybel_0(X3)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(resolution,[status(thm)],[c_7,c_20]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1814,plain,
% 7.67/1.49      ( ~ r2_waybel_0(X0,X1,X2)
% 7.67/1.49      | r2_waybel_0(X0,X3,X2)
% 7.67/1.49      | ~ m2_yellow_6(X1,X0,X3)
% 7.67/1.49      | ~ l1_waybel_0(X3,X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X3)
% 7.67/1.49      | ~ v4_orders_2(X3)
% 7.67/1.49      | ~ v7_waybel_0(X3)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_591,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1815,plain,
% 7.67/1.49      ( ~ r2_waybel_0(sK8,X0,X1)
% 7.67/1.49      | r2_waybel_0(sK8,X2,X1)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,sK8)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1814]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1817,plain,
% 7.67/1.49      ( v2_struct_0(X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,sK8)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,X2)
% 7.67/1.49      | r2_waybel_0(sK8,X2,X1)
% 7.67/1.49      | ~ r2_waybel_0(sK8,X0,X1)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2) ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1815,c_45]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1818,plain,
% 7.67/1.49      ( ~ r2_waybel_0(sK8,X0,X1)
% 7.67/1.49      | r2_waybel_0(sK8,X2,X1)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,sK8)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1817]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8331,plain,
% 7.67/1.49      ( r2_waybel_0(sK8,X0,X1) != iProver_top
% 7.67/1.49      | r2_waybel_0(sK8,X2,X1) = iProver_top
% 7.67/1.49      | m2_yellow_6(X0,sK8,X2) != iProver_top
% 7.67/1.49      | l1_waybel_0(X2,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(X2) = iProver_top
% 7.67/1.49      | v4_orders_2(X2) != iProver_top
% 7.67/1.49      | v7_waybel_0(X2) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_14624,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
% 7.67/1.49      | r2_waybel_0(sK8,X3,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
% 7.67/1.49      | m2_yellow_6(X1,sK8,X3) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X3,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v2_struct_0(X3) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v4_orders_2(X3) != iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X3) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_14621,c_8331]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_17,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_struct_0(X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_677,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X3)
% 7.67/1.49      | X1 != X3 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_678,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_677]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1869,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | v7_waybel_0(X0)
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_678,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1870,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | v7_waybel_0(X0) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1869]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1872,plain,
% 7.67/1.49      ( v2_struct_0(X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | v7_waybel_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1870,c_45]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1873,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1872]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8329,plain,
% 7.67/1.49      ( m2_yellow_6(X0,sK8,X1) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1873]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_18,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_struct_0(X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_649,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X3)
% 7.67/1.49      | X1 != X3 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_650,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X1) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_649]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1895,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_650,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1896,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1895]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1898,plain,
% 7.67/1.49      ( v2_struct_0(X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1896,c_45]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1899,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1898]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8328,plain,
% 7.67/1.49      ( m2_yellow_6(X0,sK8,X1) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v4_orders_2(X0) = iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_19,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | ~ v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_struct_0(X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_621,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | ~ v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X3)
% 7.67/1.49      | X1 != X3 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_622,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | ~ v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X1) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_621]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1921,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | ~ v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_622,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1922,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1921]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1924,plain,
% 7.67/1.49      ( v2_struct_0(X1)
% 7.67/1.49      | ~ v2_struct_0(X0)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1922,c_45]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1925,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1924]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8327,plain,
% 7.67/1.49      ( m2_yellow_6(X0,sK8,X1) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) != iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1925]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | l1_waybel_0(X0,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_struct_0(X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_705,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | l1_waybel_0(X0,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X3)
% 7.67/1.49      | X1 != X3 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_706,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | l1_waybel_0(X0,X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X1) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_705]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1843,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | l1_waybel_0(X0,X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_706,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1844,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | l1_waybel_0(X0,sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1843]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1846,plain,
% 7.67/1.49      ( v2_struct_0(X1)
% 7.67/1.49      | l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1844,c_45]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1847,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | l1_waybel_0(X0,sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1846]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8330,plain,
% 7.67/1.49      ( m2_yellow_6(X0,sK8,X1) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) = iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1847]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16121,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
% 7.67/1.49      | r2_waybel_0(sK8,X3,sK4(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2))) = iProver_top
% 7.67/1.49      | m2_yellow_6(X1,sK8,X3) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X3,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(X3) = iProver_top
% 7.67/1.49      | v4_orders_2(X3) != iProver_top
% 7.67/1.49      | v7_waybel_0(X3) != iProver_top ),
% 7.67/1.49      inference(forward_subsumption_resolution,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_14624,c_8329,c_8328,c_8327,c_8330]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1326,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | ~ r2_waybel_0(X0,X1,sK4(X0,X1,X2))
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1327,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ r2_waybel_0(sK8,X0,sK4(sK8,X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1326]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1331,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ r2_waybel_0(sK8,X0,sK4(sK8,X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1327,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8341,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,X1) = iProver_top
% 7.67/1.49      | r2_waybel_0(sK8,X0,sK4(sK8,X0,X1)) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1331]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16123,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
% 7.67/1.49      | m2_yellow_6(X1,sK8,X0) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK0(k10_yellow_6(sK8,X1),X2),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_16121,c_8341]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16239,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
% 7.67/1.49      | m2_yellow_6(X1,sK8,X0) != iProver_top
% 7.67/1.49      | l1_waybel_0(X1,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X1) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X1) != iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X1) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_11611,c_16123]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_18914,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK0(k10_yellow_6(sK8,X1),X2)) = iProver_top
% 7.67/1.49      | m2_yellow_6(X1,sK8,X0) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X1),X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(forward_subsumption_resolution,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_16239,c_8329,c_8328,c_8327,c_8330]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_29,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,sK6(X0),X1)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.67/1.49      | v1_compts_1(X0)
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1149,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,sK6(X0),X1)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.67/1.49      | v1_compts_1(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1150,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,sK6(sK8),X0)
% 7.67/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1149]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1154,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,sK6(sK8),X0)
% 7.67/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK8))
% 7.67/1.49      | v1_compts_1(sK8) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1150,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8347,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,sK6(sK8),X0) != iProver_top
% 7.67/1.49      | m1_subset_1(X0,u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1154]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_18916,plain,
% 7.67/1.49      ( m2_yellow_6(X0,sK8,sK6(sK8)) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK6(sK8),sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X1),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v2_struct_0(sK6(sK8)) = iProver_top
% 7.67/1.49      | v4_orders_2(sK6(sK8)) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK6(sK8)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_18914,c_8347]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_33,plain,
% 7.67/1.49      ( v1_compts_1(X0)
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v2_struct_0(sK6(X0))
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1093,plain,
% 7.67/1.49      ( v1_compts_1(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v2_struct_0(sK6(X0))
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_33,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1094,plain,
% 7.67/1.49      ( v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_struct_0(sK6(sK8))
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1093]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1096,plain,
% 7.67/1.49      ( v1_compts_1(sK8) | ~ v2_struct_0(sK6(sK8)) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1094,c_45,c_44,c_43,c_69]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1098,plain,
% 7.67/1.49      ( v1_compts_1(sK8) = iProver_top | v2_struct_0(sK6(sK8)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_32,plain,
% 7.67/1.49      ( v1_compts_1(X0)
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v4_orders_2(sK6(X0))
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1107,plain,
% 7.67/1.49      ( v1_compts_1(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v4_orders_2(sK6(X0))
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_32,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1108,plain,
% 7.67/1.49      ( v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | v4_orders_2(sK6(sK8))
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1107]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1110,plain,
% 7.67/1.49      ( v4_orders_2(sK6(sK8)) | v1_compts_1(sK8) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1108,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1111,plain,
% 7.67/1.49      ( v1_compts_1(sK8) | v4_orders_2(sK6(sK8)) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1110]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1112,plain,
% 7.67/1.49      ( v1_compts_1(sK8) = iProver_top | v4_orders_2(sK6(sK8)) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1111]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_31,plain,
% 7.67/1.49      ( v1_compts_1(X0)
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v7_waybel_0(sK6(X0))
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1121,plain,
% 7.67/1.49      ( v1_compts_1(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v7_waybel_0(sK6(X0))
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_31,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1122,plain,
% 7.67/1.49      ( v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | v7_waybel_0(sK6(sK8))
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1121]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1124,plain,
% 7.67/1.49      ( v7_waybel_0(sK6(sK8)) | v1_compts_1(sK8) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1122,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1125,plain,
% 7.67/1.49      ( v1_compts_1(sK8) | v7_waybel_0(sK6(sK8)) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1124]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1126,plain,
% 7.67/1.49      ( v1_compts_1(sK8) = iProver_top | v7_waybel_0(sK6(sK8)) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_30,plain,
% 7.67/1.49      ( l1_waybel_0(sK6(X0),X0)
% 7.67/1.49      | v1_compts_1(X0)
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1135,plain,
% 7.67/1.49      ( l1_waybel_0(sK6(X0),X0)
% 7.67/1.49      | v1_compts_1(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_30,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1136,plain,
% 7.67/1.49      ( l1_waybel_0(sK6(sK8),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1135]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1138,plain,
% 7.67/1.49      ( l1_waybel_0(sK6(sK8),sK8) | v1_compts_1(sK8) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1136,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1140,plain,
% 7.67/1.49      ( l1_waybel_0(sK6(sK8),sK8) = iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_34,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,sK7(X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ v1_compts_1(X0)
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1063,plain,
% 7.67/1.49      ( r3_waybel_9(X0,X1,sK7(X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ v1_compts_1(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_34,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1064,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK7(sK8,X0))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1063]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1068,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | r3_waybel_9(sK8,X0,sK7(sK8,X0))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1064,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1069,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK7(sK8,X0))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1068]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8352,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,X0,sK7(sK8,X0)) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | v1_compts_1(sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1069]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_40,negated_conjecture,
% 7.67/1.49      ( ~ v1_compts_1(sK8) | ~ v2_struct_0(sK9) ),
% 7.67/1.49      inference(cnf_transformation,[],[f114]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_55,plain,
% 7.67/1.49      ( v1_compts_1(sK8) != iProver_top | v2_struct_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_39,negated_conjecture,
% 7.67/1.49      ( ~ v1_compts_1(sK8) | v4_orders_2(sK9) ),
% 7.67/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_56,plain,
% 7.67/1.49      ( v1_compts_1(sK8) != iProver_top | v4_orders_2(sK9) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_38,negated_conjecture,
% 7.67/1.49      ( ~ v1_compts_1(sK8) | v7_waybel_0(sK9) ),
% 7.67/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_57,plain,
% 7.67/1.49      ( v1_compts_1(sK8) != iProver_top | v7_waybel_0(sK9) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_37,negated_conjecture,
% 7.67/1.49      ( l1_waybel_0(sK9,sK8) | ~ v1_compts_1(sK8) ),
% 7.67/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_58,plain,
% 7.67/1.49      ( l1_waybel_0(sK9,sK8) = iProver_top | v1_compts_1(sK8) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_35,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | m1_subset_1(sK7(X1,X0),u1_struct_0(X1))
% 7.67/1.49      | ~ v1_compts_1(X1)
% 7.67/1.49      | ~ v2_pre_topc(X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1) ),
% 7.67/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1497,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | m1_subset_1(sK7(X1,X0),u1_struct_0(X1))
% 7.67/1.49      | ~ v1_compts_1(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_35,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1498,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8))
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1497]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1502,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8))
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1498,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1503,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | m1_subset_1(sK7(sK8,X0),u1_struct_0(sK8))
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1502]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8893,plain,
% 7.67/1.49      ( ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8))
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1503]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8894,plain,
% 7.67/1.49      ( l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8)) = iProver_top
% 7.67/1.49      | v1_compts_1(sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_8893]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8899,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9))
% 7.67/1.49      | ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1069]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8900,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9)) = iProver_top
% 7.67/1.49      | l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | v1_compts_1(sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_8899]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_28,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | m2_yellow_6(sK5(X0,X1,X2),X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1170,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | m2_yellow_6(sK5(X0,X1,X2),X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_28,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1171,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | m2_yellow_6(sK5(sK8,X0,X1),sK8,X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1170]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1175,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | m2_yellow_6(sK5(sK8,X0,X1),sK8,X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1171,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1176,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | m2_yellow_6(sK5(sK8,X0,X1),sK8,X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1175]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9144,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,sK9,sK7(sK8,sK9))
% 7.67/1.49      | m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | ~ m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1176]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9145,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9)) != iProver_top
% 7.67/1.49      | m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) = iProver_top
% 7.67/1.49      | l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9144]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_27,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1203,plain,
% 7.67/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | r2_hidden(X2,k10_yellow_6(X0,sK5(X0,X1,X2)))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1204,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,sK5(sK8,X0,X1)))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1203]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1208,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,sK5(sK8,X0,X1)))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1204,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1209,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,sK5(sK8,X0,X1)))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1208]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9143,plain,
% 7.67/1.49      ( ~ r3_waybel_9(sK8,sK9,sK7(sK8,sK9))
% 7.67/1.49      | ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | ~ m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8))
% 7.67/1.49      | r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))))
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1209]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9147,plain,
% 7.67/1.49      ( r3_waybel_9(sK8,sK9,sK7(sK8,sK9)) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(sK7(sK8,sK9),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9)))) = iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9143]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_6,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9297,plain,
% 7.67/1.49      ( ~ r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))))
% 7.67/1.49      | ~ r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9)) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9298,plain,
% 7.67/1.49      ( r2_hidden(sK7(sK8,sK9),k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9)))) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9297]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_21,plain,
% 7.67/1.49      ( v3_yellow_6(X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | ~ v2_pre_topc(X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 7.67/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_36,negated_conjecture,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,sK9)
% 7.67/1.49      | ~ v3_yellow_6(X0,sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8) ),
% 7.67/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_780,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(X1,X2)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_pre_topc(X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X2)
% 7.67/1.49      | X0 != X1
% 7.67/1.49      | k10_yellow_6(X2,X1) = k1_xboole_0
% 7.67/1.49      | sK8 != X2 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_781,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_pre_topc(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = k1_xboole_0 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_780]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_785,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m2_yellow_6(X0,sK8,sK9)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = k1_xboole_0 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_781,c_45,c_44,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_786,plain,
% 7.67/1.49      ( ~ m2_yellow_6(X0,sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = k1_xboole_0 ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_785]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9326,plain,
% 7.67/1.49      ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8)
% 7.67/1.49      | ~ v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9)))
% 7.67/1.49      | ~ v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9)))
% 7.67/1.49      | ~ v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)))
% 7.67/1.49      | k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) = k1_xboole_0 ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_786]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9327,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) = k1_xboole_0
% 7.67/1.49      | m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8) != iProver_top
% 7.67/1.49      | v1_compts_1(sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9))) = iProver_top
% 7.67/1.49      | v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9))) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9))) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9326]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9336,plain,
% 7.67/1.49      ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
% 7.67/1.49      | l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1847]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9337,plain,
% 7.67/1.49      ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)),sK8) = iProver_top
% 7.67/1.49      | l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9336]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9335,plain,
% 7.67/1.49      ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9)))
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1873]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9339,plain,
% 7.67/1.49      ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK5(sK8,sK9,sK7(sK8,sK9))) = iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9335]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9334,plain,
% 7.67/1.49      ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9)))
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1899]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9341,plain,
% 7.67/1.49      ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK5(sK8,sK9,sK7(sK8,sK9))) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9334]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9557,plain,
% 7.67/1.49      ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9)))
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1925]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9725,plain,
% 7.67/1.49      ( ~ m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9)
% 7.67/1.49      | ~ l1_waybel_0(sK9,sK8)
% 7.67/1.49      | ~ v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9)))
% 7.67/1.49      | v2_struct_0(sK9)
% 7.67/1.49      | ~ v4_orders_2(sK9)
% 7.67/1.49      | ~ v7_waybel_0(sK9) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_9557]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9726,plain,
% 7.67/1.49      ( m2_yellow_6(sK5(sK8,sK9,sK7(sK8,sK9)),sK8,sK9) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK9,sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK5(sK8,sK9,sK7(sK8,sK9))) != iProver_top
% 7.67/1.49      | v2_struct_0(sK9) = iProver_top
% 7.67/1.49      | v4_orders_2(sK9) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK9) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_9725]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_7459,plain,
% 7.67/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.67/1.49      theory(equality) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9732,plain,
% 7.67/1.49      ( ~ r1_tarski(X0,sK7(sK8,sK9))
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9))
% 7.67/1.49      | k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) != X0 ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_7459]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10390,plain,
% 7.67/1.49      ( r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9))
% 7.67/1.49      | ~ r1_tarski(k1_xboole_0,sK7(sK8,sK9))
% 7.67/1.49      | k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) != k1_xboole_0 ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_9732]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10392,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))) != k1_xboole_0
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,sK5(sK8,sK9,sK7(sK8,sK9))),sK7(sK8,sK9)) = iProver_top
% 7.67/1.49      | r1_tarski(k1_xboole_0,sK7(sK8,sK9)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_10390]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10391,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,sK7(sK8,sK9)) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10394,plain,
% 7.67/1.49      ( r1_tarski(k1_xboole_0,sK7(sK8,sK9)) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_10391]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10405,plain,
% 7.67/1.49      ( v1_compts_1(sK8) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_8352,c_55,c_56,c_57,c_58,c_8894,c_8900,c_9145,c_9147,
% 7.67/1.49                 c_9298,c_9327,c_9337,c_9339,c_9341,c_9726,c_10392,c_10394]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_19144,plain,
% 7.67/1.49      ( m2_yellow_6(X0,sK8,sK6(sK8)) != iProver_top
% 7.67/1.49      | m1_subset_1(sK0(k10_yellow_6(sK8,X0),X1),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_18916,c_55,c_56,c_57,c_58,c_1098,c_1112,c_1126,c_1140,
% 7.67/1.49                 c_8894,c_8900,c_9145,c_9147,c_9298,c_9327,c_9337,c_9339,
% 7.67/1.49                 c_9341,c_9726,c_10392,c_10394]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_19153,plain,
% 7.67/1.49      ( m2_yellow_6(X0,sK8,sK6(sK8)) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),X1) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_11611,c_19144]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_20211,plain,
% 7.67/1.49      ( l1_waybel_0(sK10(sK6(sK8)),sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK6(sK8),sK8) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,sK10(sK6(sK8))),X0) = iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v2_struct_0(sK10(sK6(sK8))) = iProver_top
% 7.67/1.49      | v2_struct_0(sK6(sK8)) = iProver_top
% 7.67/1.49      | v4_orders_2(sK10(sK6(sK8))) != iProver_top
% 7.67/1.49      | v4_orders_2(sK6(sK8)) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK10(sK6(sK8))) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK6(sK8)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8355,c_19153]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8348,plain,
% 7.67/1.49      ( l1_waybel_0(sK6(sK8),sK8) = iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1138]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9161,plain,
% 7.67/1.49      ( l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(sK10(X0)) != iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8355,c_8327]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9487,plain,
% 7.67/1.49      ( v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v2_struct_0(sK10(sK6(sK8))) != iProver_top
% 7.67/1.49      | v2_struct_0(sK6(sK8)) = iProver_top
% 7.67/1.49      | v4_orders_2(sK6(sK8)) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK6(sK8)) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8348,c_9161]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9014,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | v7_waybel_0(sK10(X0)) ),
% 7.67/1.49      inference(resolution,[status(thm)],[c_1873,c_42]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9030,plain,
% 7.67/1.49      ( v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK6(sK8))
% 7.67/1.49      | ~ v4_orders_2(sK6(sK8))
% 7.67/1.49      | v7_waybel_0(sK10(sK6(sK8)))
% 7.67/1.49      | ~ v7_waybel_0(sK6(sK8)) ),
% 7.67/1.49      inference(resolution,[status(thm)],[c_9014,c_1138]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_72,plain,
% 7.67/1.49      ( v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_pre_topc(sK8)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | v4_orders_2(sK6(sK8))
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_75,plain,
% 7.67/1.49      ( v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_pre_topc(sK8)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | v7_waybel_0(sK6(sK8))
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_31]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10243,plain,
% 7.67/1.49      ( v7_waybel_0(sK10(sK6(sK8))) | v1_compts_1(sK8) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_9030,c_45,c_44,c_43,c_72,c_75,c_1094]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10244,plain,
% 7.67/1.49      ( v1_compts_1(sK8) | v7_waybel_0(sK10(sK6(sK8))) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_10243]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10245,plain,
% 7.67/1.49      ( v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v7_waybel_0(sK10(sK6(sK8))) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_10244]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9098,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | v4_orders_2(sK10(X0))
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(resolution,[status(thm)],[c_1899,c_42]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9177,plain,
% 7.67/1.49      ( v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK6(sK8))
% 7.67/1.49      | v4_orders_2(sK10(sK6(sK8)))
% 7.67/1.49      | ~ v4_orders_2(sK6(sK8))
% 7.67/1.49      | ~ v7_waybel_0(sK6(sK8)) ),
% 7.67/1.49      inference(resolution,[status(thm)],[c_9098,c_1138]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10304,plain,
% 7.67/1.49      ( v1_compts_1(sK8) | v4_orders_2(sK10(sK6(sK8))) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_9177,c_45,c_44,c_43,c_69,c_72,c_75]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10306,plain,
% 7.67/1.49      ( v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v4_orders_2(sK10(sK6(sK8))) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_10304]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10889,plain,
% 7.67/1.49      ( m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8))
% 7.67/1.49      | ~ l1_waybel_0(sK6(sK8),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK6(sK8))
% 7.67/1.49      | ~ v4_orders_2(sK6(sK8))
% 7.67/1.49      | ~ v7_waybel_0(sK6(sK8)) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_42]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10919,plain,
% 7.67/1.49      ( m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8)) = iProver_top
% 7.67/1.49      | l1_waybel_0(sK6(sK8),sK8) != iProver_top
% 7.67/1.49      | v1_compts_1(sK8) = iProver_top
% 7.67/1.49      | v2_struct_0(sK6(sK8)) = iProver_top
% 7.67/1.49      | v4_orders_2(sK6(sK8)) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK6(sK8)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_10889]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_12425,plain,
% 7.67/1.49      ( ~ m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8))
% 7.67/1.49      | l1_waybel_0(sK10(sK6(sK8)),sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK6(sK8),sK8)
% 7.67/1.49      | v2_struct_0(sK6(sK8))
% 7.67/1.49      | ~ v4_orders_2(sK6(sK8))
% 7.67/1.49      | ~ v7_waybel_0(sK6(sK8)) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_1847]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_12426,plain,
% 7.67/1.49      ( m2_yellow_6(sK10(sK6(sK8)),sK8,sK6(sK8)) != iProver_top
% 7.67/1.49      | l1_waybel_0(sK10(sK6(sK8)),sK8) = iProver_top
% 7.67/1.49      | l1_waybel_0(sK6(sK8),sK8) != iProver_top
% 7.67/1.49      | v2_struct_0(sK6(sK8)) = iProver_top
% 7.67/1.49      | v4_orders_2(sK6(sK8)) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK6(sK8)) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_12425]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_20348,plain,
% 7.67/1.49      ( r1_tarski(k10_yellow_6(sK8,sK10(sK6(sK8))),X0) = iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_20211,c_55,c_56,c_57,c_58,c_1098,c_1112,c_1126,c_1140,
% 7.67/1.49                 c_8894,c_8900,c_9145,c_9147,c_9298,c_9327,c_9337,c_9339,
% 7.67/1.49                 c_9341,c_9487,c_9726,c_10245,c_10306,c_10392,c_10394,c_10919,
% 7.67/1.49                 c_12426]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_13,plain,
% 7.67/1.49      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.67/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1353,plain,
% 7.67/1.49      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.67/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1354,plain,
% 7.67/1.49      ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1353]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1358,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1354,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1359,plain,
% 7.67/1.49      ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1358]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1550,plain,
% 7.67/1.49      ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_1533,c_1359]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8336,plain,
% 7.67/1.49      ( m1_connsp_2(sK3(sK8,X0,X1),sK8,X1) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0)) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1550]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10,plain,
% 7.67/1.49      ( ~ m1_connsp_2(X0,X1,sK1(X1,X2,X3))
% 7.67/1.49      | r1_waybel_0(X1,X2,X0)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.67/1.49      | r2_hidden(sK1(X1,X2,X3),X3)
% 7.67/1.49      | ~ v2_pre_topc(X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | k10_yellow_6(X1,X2) = X3 ),
% 7.67/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1635,plain,
% 7.67/1.49      ( ~ m1_connsp_2(X0,X1,sK1(X1,X2,X3))
% 7.67/1.49      | r1_waybel_0(X1,X2,X0)
% 7.67/1.49      | ~ l1_waybel_0(X2,X1)
% 7.67/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.67/1.49      | r2_hidden(sK1(X1,X2,X3),X3)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | k10_yellow_6(X1,X2) = X3
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1636,plain,
% 7.67/1.49      ( ~ m1_connsp_2(X0,sK8,sK1(sK8,X1,X2))
% 7.67/1.49      | r1_waybel_0(sK8,X1,X0)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(sK1(sK8,X1,X2),X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(sK8)
% 7.67/1.49      | k10_yellow_6(sK8,X1) = X2 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1635]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1640,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ m1_connsp_2(X0,sK8,sK1(sK8,X1,X2))
% 7.67/1.49      | r1_waybel_0(sK8,X1,X0)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(sK1(sK8,X1,X2),X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | k10_yellow_6(sK8,X1) = X2 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1636,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1641,plain,
% 7.67/1.49      ( ~ m1_connsp_2(X0,sK8,sK1(sK8,X1,X2))
% 7.67/1.49      | r1_waybel_0(sK8,X1,X0)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(sK1(sK8,X1,X2),X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | k10_yellow_6(sK8,X1) = X2 ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1640]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8332,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | m1_connsp_2(X2,sK8,sK1(sK8,X0,X1)) != iProver_top
% 7.67/1.49      | r1_waybel_0(sK8,X0,X2) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1641]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_12773,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
% 7.67/1.49      | l1_waybel_0(X2,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
% 7.67/1.49      | v2_struct_0(X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X2) != iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X2) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8336,c_8332]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2378,plain,
% 7.67/1.49      ( r1_waybel_0(sK8,X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X2,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X3,u1_struct_0(sK8))
% 7.67/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(X3,k10_yellow_6(sK8,X2))
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X4),X4)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | sK3(sK8,X2,X3) != X1
% 7.67/1.49      | sK1(sK8,X0,X4) != X3
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X4
% 7.67/1.49      | sK8 != sK8 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_1550,c_1641]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2379,plain,
% 7.67/1.49      ( r1_waybel_0(sK8,X0,sK3(sK8,X1,sK1(sK8,X0,X2)))
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | ~ m1_subset_1(sK1(sK8,X0,X2),u1_struct_0(sK8))
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X2),X2)
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X2),k10_yellow_6(sK8,X1))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X2 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_2378]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_11,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.67/1.49      | m1_subset_1(sK1(X1,X0,X2),u1_struct_0(X1))
% 7.67/1.49      | ~ v2_pre_topc(X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | k10_yellow_6(X1,X0) = X2 ),
% 7.67/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1602,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.67/1.49      | m1_subset_1(sK1(X1,X0,X2),u1_struct_0(X1))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | k10_yellow_6(X1,X0) = X2
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1603,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X1 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1602]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1607,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X1 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1603,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1608,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X1 ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1607]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2411,plain,
% 7.67/1.49      ( r1_waybel_0(sK8,X0,sK3(sK8,X1,sK1(sK8,X0,X2)))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X2),X2)
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X2),k10_yellow_6(sK8,X1))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X2 ),
% 7.67/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_2379,c_1608]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2425,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X2,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(X2) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v4_orders_2(X2) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X2) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_2411]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16351,plain,
% 7.67/1.49      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X2,sK8) != iProver_top
% 7.67/1.49      | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
% 7.67/1.49      | v2_struct_0(X2) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X2) != iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X2) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_12773,c_2425]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16352,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X2,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X1) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(X2) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v4_orders_2(X2) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X2) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_16351]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.67/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8364,plain,
% 7.67/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.67/1.49      | r2_hidden(X0,X2) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16368,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | r1_waybel_0(sK8,X0,sK3(sK8,X2,sK1(sK8,X0,X1))) = iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | l1_waybel_0(X2,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X3) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X2)) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X3) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v2_struct_0(X2) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v4_orders_2(X2) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X2) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_16352,c_8364]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_12,plain,
% 7.67/1.49      ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.67/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.67/1.49      | ~ v2_pre_topc(X0)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f119]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1389,plain,
% 7.67/1.49      ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
% 7.67/1.49      | ~ l1_waybel_0(X1,X0)
% 7.67/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.67/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | ~ l1_pre_topc(X0)
% 7.67/1.49      | sK8 != X0 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_44]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1390,plain,
% 7.67/1.49      ( ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(sK8) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_1389]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1394,plain,
% 7.67/1.49      ( ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0) ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_1390,c_45,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1395,plain,
% 7.67/1.49      ( ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | ~ m1_subset_1(k10_yellow_6(sK8,X0),k1_zfmisc_1(u1_struct_0(sK8)))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_1394]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1551,plain,
% 7.67/1.49      ( ~ r1_waybel_0(sK8,X0,sK3(sK8,X0,X1))
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK8))
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0))
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_1533,c_1395]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8335,plain,
% 7.67/1.49      ( r1_waybel_0(sK8,X0,sK3(sK8,X0,X1)) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r2_hidden(X1,k10_yellow_6(sK8,X0)) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1551]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_17045,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8)) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X0)) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_16368,c_8335]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_1609,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | m1_subset_1(sK1(sK8,X0,X1),u1_struct_0(sK8)) = iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_1608]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22044,plain,
% 7.67/1.49      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X0)) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_17045,c_1609]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22045,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),k10_yellow_6(sK8,X0)) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_22044]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8360,plain,
% 7.67/1.49      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22060,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,X0) = X1
% 7.67/1.49      | l1_waybel_0(X0,sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,X0,X1),X2) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X2) != iProver_top
% 7.67/1.49      | r1_tarski(k10_yellow_6(sK8,X0),sK1(sK8,X0,X1)) != iProver_top
% 7.67/1.49      | v2_struct_0(X0) = iProver_top
% 7.67/1.49      | v4_orders_2(X0) != iProver_top
% 7.67/1.49      | v7_waybel_0(X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_22045,c_8360]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22332,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,sK10(sK6(sK8))) = X0
% 7.67/1.49      | l1_waybel_0(sK10(sK6(sK8)),sK8) != iProver_top
% 7.67/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
% 7.67/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.67/1.49      | v2_struct_0(sK10(sK6(sK8))) = iProver_top
% 7.67/1.49      | v4_orders_2(sK10(sK6(sK8))) != iProver_top
% 7.67/1.49      | v7_waybel_0(sK10(sK6(sK8))) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_20348,c_22060]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23897,plain,
% 7.67/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
% 7.67/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | k10_yellow_6(sK8,sK10(sK6(sK8))) = X0 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_22332,c_55,c_56,c_57,c_58,c_1098,c_1112,c_1126,c_1140,
% 7.67/1.49                 c_8894,c_8900,c_9145,c_9147,c_9298,c_9327,c_9337,c_9339,
% 7.67/1.49                 c_9341,c_9487,c_9726,c_10245,c_10306,c_10392,c_10394,c_10919,
% 7.67/1.49                 c_12426]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23898,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,sK10(sK6(sK8))) = X0
% 7.67/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
% 7.67/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_23897]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_23907,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,sK10(sK6(sK8))) = X0
% 7.67/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,sK10(sK6(sK8)),X0),X1) = iProver_top
% 7.67/1.49      | r1_tarski(X2,X1) != iProver_top
% 7.67/1.49      | r1_tarski(X0,X2) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_23898,c_8364]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24587,plain,
% 7.67/1.49      ( k10_yellow_6(sK8,sK10(sK6(sK8))) = k1_xboole_0
% 7.67/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK8))) != iProver_top
% 7.67/1.49      | r2_hidden(sK1(sK8,sK10(sK6(sK8)),k1_xboole_0),X0) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8363,c_23907]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_4,plain,
% 7.67/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.67/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8926,plain,
% 7.67/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8928,plain,
% 7.67/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_8926]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10407,plain,
% 7.67/1.49      ( ~ v1_compts_1(sK8) ),
% 7.67/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_10405]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2695,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | l1_waybel_0(X2,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | X0 != X1
% 7.67/1.49      | sK10(X1) != X2
% 7.67/1.49      | sK8 != sK8 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_42,c_1847]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2696,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | l1_waybel_0(sK10(X0),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_2695]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2671,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | v7_waybel_0(X2)
% 7.67/1.49      | X0 != X1
% 7.67/1.49      | sK10(X1) != X2
% 7.67/1.49      | sK8 != sK8 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_42,c_1873]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2672,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | v7_waybel_0(sK10(X0)) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_2671]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2647,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | v4_orders_2(X2)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | X0 != X1
% 7.67/1.49      | sK10(X1) != X2
% 7.67/1.49      | sK8 != sK8 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_42,c_1899]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2648,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | v4_orders_2(sK10(X0))
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_2647]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2623,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(X1,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_struct_0(X2)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v4_orders_2(X1)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(X1)
% 7.67/1.49      | X0 != X1
% 7.67/1.49      | sK10(X1) != X2
% 7.67/1.49      | sK8 != sK8 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_42,c_1925]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2624,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v2_struct_0(sK10(X0))
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_2623]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_22,plain,
% 7.67/1.49      ( ~ v3_yellow_6(X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | ~ v2_pre_topc(X1)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 7.67/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_41,negated_conjecture,
% 7.67/1.49      ( v3_yellow_6(sK10(X0),sK8)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0) ),
% 7.67/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_813,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.67/1.49      | ~ l1_waybel_0(X2,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_pre_topc(X1)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(X1)
% 7.67/1.49      | v2_struct_0(X2)
% 7.67/1.49      | ~ v4_orders_2(X2)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X2)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ l1_pre_topc(X1)
% 7.67/1.49      | k10_yellow_6(X1,X0) != k1_xboole_0
% 7.67/1.49      | sK10(X2) != X0
% 7.67/1.49      | sK8 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_22,c_41]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_814,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK10(X0),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | ~ v2_pre_topc(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK10(X0))
% 7.67/1.49      | v2_struct_0(sK8)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v4_orders_2(sK10(X0))
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(sK10(X0))
% 7.67/1.49      | ~ l1_pre_topc(sK8)
% 7.67/1.49      | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_813]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_818,plain,
% 7.67/1.49      ( ~ v7_waybel_0(sK10(X0))
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v4_orders_2(sK10(X0))
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK10(X0),sK8)
% 7.67/1.49      | ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK10(X0))
% 7.67/1.49      | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_814,c_45,c_44,c_43]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_819,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK10(X0),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | v2_struct_0(sK10(X0))
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v4_orders_2(sK10(X0))
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(sK10(X0))
% 7.67/1.49      | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
% 7.67/1.49      inference(renaming,[status(thm)],[c_818]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2876,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK10(X0),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v4_orders_2(sK10(X0))
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(sK10(X0))
% 7.67/1.49      | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
% 7.67/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_2624,c_819]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2887,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK10(X0),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | ~ v7_waybel_0(sK10(X0))
% 7.67/1.49      | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
% 7.67/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_2648,c_2876]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2898,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | ~ l1_waybel_0(sK10(X0),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
% 7.67/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_2672,c_2887]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_2904,plain,
% 7.67/1.49      ( ~ l1_waybel_0(X0,sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(X0)
% 7.67/1.49      | ~ v4_orders_2(X0)
% 7.67/1.49      | ~ v7_waybel_0(X0)
% 7.67/1.49      | k10_yellow_6(sK8,sK10(X0)) != k1_xboole_0 ),
% 7.67/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_2696,c_2898]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_16733,plain,
% 7.67/1.49      ( ~ l1_waybel_0(sK6(sK8),sK8)
% 7.67/1.49      | v1_compts_1(sK8)
% 7.67/1.49      | v2_struct_0(sK6(sK8))
% 7.67/1.49      | ~ v4_orders_2(sK6(sK8))
% 7.67/1.49      | ~ v7_waybel_0(sK6(sK8))
% 7.67/1.49      | k10_yellow_6(sK8,sK10(sK6(sK8))) != k1_xboole_0 ),
% 7.67/1.49      inference(instantiation,[status(thm)],[c_2904]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24831,plain,
% 7.67/1.49      ( r2_hidden(sK1(sK8,sK10(sK6(sK8)),k1_xboole_0),X0) = iProver_top
% 7.67/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,
% 7.67/1.49                [status(thm)],
% 7.67/1.49                [c_24587,c_45,c_44,c_43,c_69,c_72,c_75,c_78,c_8928,c_10407,
% 7.67/1.49                 c_16733]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24839,plain,
% 7.67/1.49      ( r2_hidden(sK1(sK8,sK10(sK6(sK8)),k1_xboole_0),X0) = iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8363,c_24831]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_8362,plain,
% 7.67/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_9846,plain,
% 7.67/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.67/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_8362,c_8361]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_571,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.67/1.49      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_572,plain,
% 7.67/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.67/1.49      inference(unflattening,[status(thm)],[c_571]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_573,plain,
% 7.67/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.67/1.49      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_10576,plain,
% 7.67/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.67/1.49      inference(global_propositional_subsumption,[status(thm)],[c_9846,c_573]) ).
% 7.67/1.49  
% 7.67/1.49  cnf(c_24857,plain,
% 7.67/1.49      ( $false ),
% 7.67/1.49      inference(superposition,[status(thm)],[c_24839,c_10576]) ).
% 7.67/1.49  
% 7.67/1.49  
% 7.67/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.49  
% 7.67/1.49  ------                               Statistics
% 7.67/1.49  
% 7.67/1.49  ------ Selected
% 7.67/1.49  
% 7.67/1.49  total_time:                             0.676
% 7.67/1.49  
%------------------------------------------------------------------------------
