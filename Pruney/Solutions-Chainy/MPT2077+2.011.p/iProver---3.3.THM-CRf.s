%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:26 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_66)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f60,plain,(
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

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f65,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK9(X3),X0)
        & m2_yellow_6(sK9(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
            | ~ m2_yellow_6(X2,X0,sK8) )
        & l1_waybel_0(sK8,X0)
        & v7_waybel_0(sK8)
        & v4_orders_2(sK8)
        & ~ v2_struct_0(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
                ( ~ v3_yellow_6(X2,sK7)
                | ~ m2_yellow_6(X2,sK7,X1) )
            & l1_waybel_0(X1,sK7)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK7) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK7)
                & m2_yellow_6(X4,sK7,X3) )
            | ~ l1_waybel_0(X3,sK7)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK7) )
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK7)
            | ~ m2_yellow_6(X2,sK7,sK8) )
        & l1_waybel_0(sK8,sK7)
        & v7_waybel_0(sK8)
        & v4_orders_2(sK8)
        & ~ v2_struct_0(sK8) )
      | ~ v1_compts_1(sK7) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK9(X3),sK7)
            & m2_yellow_6(sK9(X3),sK7,X3) )
          | ~ l1_waybel_0(X3,sK7)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK7) )
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).

fof(f103,plain,(
    ! [X3] :
      ( m2_yellow_6(sK9(X3),sK7,X3)
      | ~ l1_waybel_0(X3,sK7)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f79,plain,(
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

fof(f101,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f100,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f102,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
              & m1_connsp_2(X4,X0,sK0(X0,X1,X2)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2)) )
          | r2_hidden(sK0(X0,X1,X2),X2) )
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
                        & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2)) )
                      | ~ r2_hidden(sK0(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2)) )
                      | r2_hidden(sK0(X0,X1,X2),X2) )
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
                            & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).

fof(f73,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK2(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f49])).

fof(f111,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK2(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f76,plain,(
    ! [X2,X0,X5,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | r1_waybel_0(X0,X1,X5)
      | ~ m1_connsp_2(X5,X0,sK0(X0,X1,X2))
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k10_yellow_6(X0,X1) = X2
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
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
    inference(cnf_transformation,[],[f49])).

fof(f110,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f32])).

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
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_9(X0,X1,X3)
      | ~ r3_waybel_9(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f83,plain,(
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

fof(f82,plain,(
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

fof(f81,plain,(
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

fof(f80,plain,(
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

fof(f14,axiom,(
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
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_hidden(X1,k6_yellow_6(X0))
            | ~ l1_waybel_0(X1,X0)
            | ~ v7_waybel_0(X1)
            | ~ v4_orders_2(X1)
            | v2_struct_0(X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r3_waybel_9(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r2_hidden(X1,k6_yellow_6(X0))
              | ~ l1_waybel_0(X1,X0)
              | ~ v7_waybel_0(X1)
              | ~ v4_orders_2(X1)
              | v2_struct_0(X1) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & r2_hidden(X1,k6_yellow_6(X0))
              & l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r3_waybel_9(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK6(X0,X3))
        & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK5(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK5(X0),X0)
        & v7_waybel_0(sK5(X0))
        & v4_orders_2(sK5(X0))
        & ~ v2_struct_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK5(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(sK5(X0),k6_yellow_6(X0))
            & l1_waybel_0(sK5(X0),X0)
            & v7_waybel_0(sK5(X0))
            & v4_orders_2(sK5(X0))
            & ~ v2_struct_0(sK5(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK6(X0,X3))
                & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f56,f58,f57])).

fof(f99,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f97,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK5(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f104,plain,(
    ! [X3] :
      ( v3_yellow_6(sK9(X3),sK7)
      | ~ l1_waybel_0(X3,sK7)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK4(X0,X1))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f53])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK4(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
        & m2_yellow_6(sK3(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
                & m2_yellow_6(sK3(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f51])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK3(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f109,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK7)
      | ~ m2_yellow_6(X2,sK7,sK8)
      | ~ v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f105,plain,
    ( ~ v2_struct_0(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f106,plain,
    ( v4_orders_2(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f107,plain,
    ( v7_waybel_0(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f108,plain,
    ( l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f66])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_39,negated_conjecture,
    ( m2_yellow_6(sK9(X0),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_11789,plain,
    ( m2_yellow_6(sK9(X0),sK7,X0) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2124,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_41])).

cnf(c_2125,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_2124])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2129,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2125,c_42,c_40])).

cnf(c_2130,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_2129])).

cnf(c_10,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1917,plain,
    ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_41])).

cnf(c_1918,plain,
    ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1917])).

cnf(c_1922,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1918,c_42,c_40])).

cnf(c_1923,plain,
    ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1922])).

cnf(c_2147,plain,
    ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2130,c_1923])).

cnf(c_11767,plain,
    ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_7,plain,
    ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
    | r1_waybel_0(X1,X2,X0)
    | ~ l1_waybel_0(X2,X1)
    | r2_hidden(sK0(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X2) = X3 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2232,plain,
    ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
    | r1_waybel_0(X1,X2,X0)
    | ~ l1_waybel_0(X2,X1)
    | r2_hidden(sK0(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X2) = X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_41])).

cnf(c_2233,plain,
    ( ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | r2_hidden(sK0(sK7,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(sK7)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_2232])).

cnf(c_2237,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | r2_hidden(sK0(sK7,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X1)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_42,c_40])).

cnf(c_2238,plain,
    ( ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | r2_hidden(sK0(sK7,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(renaming,[status(thm)],[c_2237])).

cnf(c_11763,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | m1_connsp_2(X2,sK7,sK0(sK7,X0,X1)) != iProver_top
    | r1_waybel_0(sK7,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2238])).

cnf(c_13749,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11767,c_11763])).

cnf(c_2761,plain,
    ( r1_waybel_0(sK7,X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X3,k10_yellow_6(sK7,X2))
    | r2_hidden(sK0(sK7,X0,X4),X4)
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X0)
    | sK2(sK7,X2,X3) != X1
    | sK0(sK7,X0,X4) != X3
    | k10_yellow_6(sK7,X0) = X4
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_2147,c_2238])).

cnf(c_2762,plain,
    ( r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,X2)))
    | ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | r2_hidden(sK0(sK7,X0,X2),X2)
    | r2_hidden(sK0(sK7,X0,X2),k10_yellow_6(sK7,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK0(sK7,X0,X2),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = X2 ),
    inference(unflattening,[status(thm)],[c_2761])).

cnf(c_8,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2199,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_41])).

cnf(c_2200,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_2199])).

cnf(c_2204,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_42,c_40])).

cnf(c_2205,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(renaming,[status(thm)],[c_2204])).

cnf(c_2794,plain,
    ( r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,X2)))
    | ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | r2_hidden(sK0(sK7,X0,X2),X2)
    | r2_hidden(sK0(sK7,X0,X2),k10_yellow_6(sK7,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2762,c_2205])).

cnf(c_2808,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2794])).

cnf(c_14152,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
    | k10_yellow_6(sK7,X0) = X1
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13749,c_2808])).

cnf(c_14153,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_14152])).

cnf(c_9,plain,
    ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1953,plain,
    ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_41])).

cnf(c_1954,plain,
    ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1953])).

cnf(c_1958,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1954,c_42,c_40])).

cnf(c_1959,plain,
    ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1958])).

cnf(c_2148,plain,
    ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2130,c_1959])).

cnf(c_11766,plain,
    ( r1_waybel_0(sK7,X0,sK2(sK7,X0,X1)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2148])).

cnf(c_14160,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14153,c_11766])).

cnf(c_43,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_45,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2201,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2200])).

cnf(c_15575,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X0)) = iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | k10_yellow_6(sK7,X0) = X1
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14160,c_43,c_45,c_2201])).

cnf(c_15576,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15575])).

cnf(c_0,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11795,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_475,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X1 != X2
    | X0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_11787,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_12529,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11795,c_11787])).

cnf(c_15588,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15576,c_12529])).

cnf(c_12315,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_12316,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12315])).

cnf(c_15616,plain,
    ( r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15588,c_12316])).

cnf(c_15617,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15616])).

cnf(c_11768,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2130])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_11794,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12293,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11768,c_11794])).

cnf(c_15624,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15617,c_12293])).

cnf(c_11764,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2205])).

cnf(c_14159,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X1)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14153,c_12529])).

cnf(c_14414,plain,
    ( r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X1)) = iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,k1_xboole_0))) = iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14159,c_12316])).

cnf(c_14415,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_14414])).

cnf(c_14420,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
    | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14415,c_11766])).

cnf(c_19,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1884,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_41])).

cnf(c_1885,plain,
    ( r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1884])).

cnf(c_1889,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1885,c_42,c_40])).

cnf(c_1890,plain,
    ( r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1889])).

cnf(c_11773,plain,
    ( r3_waybel_9(sK7,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_1891,plain,
    ( r3_waybel_9(sK7,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_12947,plain,
    ( r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r3_waybel_9(sK7,X0,X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11773,c_1891,c_12293])).

cnf(c_12948,plain,
    ( r3_waybel_9(sK7,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12947])).

cnf(c_14528,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14420,c_12948])).

cnf(c_14637,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11764,c_14528])).

cnf(c_14647,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14637,c_12316])).

cnf(c_14648,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_14647])).

cnf(c_20,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1852,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r3_waybel_9(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_41])).

cnf(c_1853,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,X2,X1)
    | ~ m2_yellow_6(X0,sK7,X2)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X2)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1852])).

cnf(c_1855,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,X2,X1)
    | ~ m2_yellow_6(X0,sK7,X2)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1853,c_42,c_40])).

cnf(c_1856,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,X2,X1)
    | ~ m2_yellow_6(X0,sK7,X2)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1855])).

cnf(c_11774,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | r3_waybel_9(sK7,X2,X1) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1856])).

cnf(c_15630,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) != iProver_top
    | r3_waybel_9(sK7,X2,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X1,sK7,X2) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15624,c_11774])).

cnf(c_15747,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14648,c_15630])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_574,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_575,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_2420,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_575,c_40])).

cnf(c_2421,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | l1_waybel_0(X0,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2420])).

cnf(c_2423,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2421,c_42])).

cnf(c_2424,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | l1_waybel_0(X0,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2423])).

cnf(c_2425,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2424])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_546,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_547,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_2446,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_547,c_40])).

cnf(c_2447,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2446])).

cnf(c_2449,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2447,c_42])).

cnf(c_2450,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_2449])).

cnf(c_2451,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2450])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_518,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_519,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_2472,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_519,c_40])).

cnf(c_2473,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2472])).

cnf(c_2475,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2473,c_42])).

cnf(c_2476,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2475])).

cnf(c_2477,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2476])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_490,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_491,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_2498,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_491,c_40])).

cnf(c_2499,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2498])).

cnf(c_2501,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2499,c_42])).

cnf(c_2502,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2501])).

cnf(c_2503,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_15824,plain,
    ( v4_orders_2(X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK7,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15747,c_2425,c_2451,c_2477,c_2503])).

cnf(c_15825,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_15824])).

cnf(c_25,plain,
    ( ~ r3_waybel_9(X0,sK5(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1735,plain,
    ( ~ r3_waybel_9(X0,sK5(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_1736,plain,
    ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1735])).

cnf(c_1740,plain,
    ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1736,c_42,c_40])).

cnf(c_11778,plain,
    ( r3_waybel_9(sK7,sK5(sK7),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1740])).

cnf(c_15829,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15825,c_11778])).

cnf(c_30,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK5(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1665,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK5(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_1666,plain,
    ( v1_compts_1(sK7)
    | ~ v2_struct_0(sK5(sK7))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1665])).

cnf(c_1668,plain,
    ( v1_compts_1(sK7)
    | ~ v2_struct_0(sK5(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1666,c_42,c_41,c_40,c_66])).

cnf(c_1670,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_29,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK5(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1679,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK5(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_1680,plain,
    ( v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | v4_orders_2(sK5(sK7))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1679])).

cnf(c_1682,plain,
    ( v4_orders_2(sK5(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1680,c_42,c_40])).

cnf(c_1683,plain,
    ( v1_compts_1(sK7)
    | v4_orders_2(sK5(sK7)) ),
    inference(renaming,[status(thm)],[c_1682])).

cnf(c_1684,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v4_orders_2(sK5(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1683])).

cnf(c_28,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK5(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1693,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK5(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_41])).

cnf(c_1694,plain,
    ( v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | v7_waybel_0(sK5(sK7))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1693])).

cnf(c_1696,plain,
    ( v7_waybel_0(sK5(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1694,c_42,c_40])).

cnf(c_1697,plain,
    ( v1_compts_1(sK7)
    | v7_waybel_0(sK5(sK7)) ),
    inference(renaming,[status(thm)],[c_1696])).

cnf(c_1698,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v7_waybel_0(sK5(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1697])).

cnf(c_27,plain,
    ( l1_waybel_0(sK5(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1707,plain,
    ( l1_waybel_0(sK5(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_1708,plain,
    ( l1_waybel_0(sK5(sK7),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1707])).

cnf(c_1710,plain,
    ( l1_waybel_0(sK5(sK7),sK7)
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1708,c_42,c_40])).

cnf(c_1712,plain,
    ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1710])).

cnf(c_15862,plain,
    ( v1_compts_1(sK7) = iProver_top
    | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15829,c_1670,c_1684,c_1698,c_1712])).

cnf(c_15863,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_15862])).

cnf(c_15869,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15624,c_15863])).

cnf(c_12085,plain,
    ( ~ m2_yellow_6(X0,sK7,sK5(sK7))
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK5(sK7),sK7)
    | v2_struct_0(sK5(sK7))
    | ~ v4_orders_2(sK5(sK7))
    | ~ v7_waybel_0(sK5(sK7)) ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_12086,plain,
    ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12085])).

cnf(c_12084,plain,
    ( ~ m2_yellow_6(X0,sK7,sK5(sK7))
    | ~ l1_waybel_0(sK5(sK7),sK7)
    | v2_struct_0(sK5(sK7))
    | ~ v4_orders_2(sK5(sK7))
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK5(sK7)) ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_12090,plain,
    ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12084])).

cnf(c_12083,plain,
    ( ~ m2_yellow_6(X0,sK7,sK5(sK7))
    | ~ l1_waybel_0(sK5(sK7),sK7)
    | v2_struct_0(sK5(sK7))
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK5(sK7))
    | ~ v7_waybel_0(sK5(sK7)) ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_12094,plain,
    ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12083])).

cnf(c_15915,plain,
    ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15869,c_1670,c_1684,c_1698,c_1712,c_12086,c_12090,c_12094,c_15624,c_15863])).

cnf(c_15916,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_15915])).

cnf(c_15921,plain,
    ( k10_yellow_6(sK7,sK9(sK5(sK7))) = k1_xboole_0
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK5(sK7))) = iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11789,c_15916])).

cnf(c_1392,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | ~ v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | sK9(X2) != X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_491,c_39])).

cnf(c_1393,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(X0))
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1392])).

cnf(c_1397,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1393,c_42,c_40])).

cnf(c_1398,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1397])).

cnf(c_1362,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X3)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | sK9(X2) != X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_519,c_39])).

cnf(c_1363,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1362])).

cnf(c_1367,plain,
    ( ~ v7_waybel_0(X0)
    | v4_orders_2(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_42,c_40])).

cnf(c_1368,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1367])).

cnf(c_1332,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X3)
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | sK9(X2) != X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_547,c_39])).

cnf(c_1333,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK9(X0))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1332])).

cnf(c_1337,plain,
    ( v7_waybel_0(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1333,c_42,c_40])).

cnf(c_1338,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK9(X0)) ),
    inference(renaming,[status(thm)],[c_1337])).

cnf(c_1302,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X1)
    | X3 != X0
    | sK9(X3) != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_575,c_39])).

cnf(c_1303,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1302])).

cnf(c_1307,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1303,c_42,c_40])).

cnf(c_1308,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1307])).

cnf(c_18,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,negated_conjecture,
    ( v3_yellow_6(sK9(X0),sK7)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_672,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
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
    | sK9(X2) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_673,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK9(X0))
    | ~ l1_pre_topc(sK7)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_677,plain,
    ( ~ v7_waybel_0(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v4_orders_2(X0)
    | v1_compts_1(sK7)
    | ~ l1_waybel_0(sK9(X0),sK7)
    | ~ l1_waybel_0(X0,sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_673,c_42,c_41,c_40])).

cnf(c_678,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK9(X0))
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_677])).

cnf(c_1578,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK9(X0))
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1308,c_678])).

cnf(c_1592,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1338,c_1578])).

cnf(c_1601,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1368,c_1592])).

cnf(c_1610,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_1601])).

cnf(c_12243,plain,
    ( ~ l1_waybel_0(sK5(sK7),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK5(sK7))
    | ~ v4_orders_2(sK5(sK7))
    | ~ v7_waybel_0(sK5(sK7))
    | k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_12244,plain,
    ( k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12243])).

cnf(c_11780,plain,
    ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1710])).

cnf(c_11759,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_12020,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11789,c_11759])).

cnf(c_12238,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK5(sK7))) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11780,c_12020])).

cnf(c_13274,plain,
    ( v2_struct_0(sK9(sK5(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12238,c_1670,c_1684,c_1698])).

cnf(c_13275,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK5(sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13274])).

cnf(c_15961,plain,
    ( v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15921,c_1670,c_1684,c_1698,c_1712,c_12244,c_13275])).

cnf(c_23,plain,
    ( r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1756,plain,
    ( r3_waybel_9(X0,X1,sK4(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_41])).

cnf(c_1757,plain,
    ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1756])).

cnf(c_1761,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1757,c_42,c_40])).

cnf(c_1762,plain,
    ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1761])).

cnf(c_11777,plain,
    ( r3_waybel_9(sK7,X0,sK4(sK7,X0)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1762])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1786,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_41])).

cnf(c_1787,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1786])).

cnf(c_1791,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1787,c_42,c_40])).

cnf(c_1792,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1791])).

cnf(c_11776,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_17,plain,
    ( v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ v3_yellow_6(X0,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_639,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(X1,X2)
    | ~ v1_compts_1(sK7)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k10_yellow_6(X2,X1) = k1_xboole_0
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_640,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | ~ v2_pre_topc(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7)
    | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_644,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m2_yellow_6(X0,sK7,sK8)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_42,c_41,c_40])).

cnf(c_645,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_644])).

cnf(c_11786,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_37,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_52,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_53,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v4_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_54,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v7_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_55,plain,
    ( l1_waybel_0(sK8,sK7) = iProver_top
    | v1_compts_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_646,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_11895,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2424])).

cnf(c_11896,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11895])).

cnf(c_11900,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_11901,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11900])).

cnf(c_11907,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2476])).

cnf(c_11908,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11907])).

cnf(c_12841,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11786,c_52,c_53,c_54,c_55,c_646,c_11896,c_11901,c_11908])).

cnf(c_12842,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK8) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_12841])).

cnf(c_13307,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK3(sK7,sK8,X0)) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11776,c_12842])).

cnf(c_13774,plain,
    ( v2_struct_0(sK3(sK7,sK8,X0)) = iProver_top
    | v1_compts_1(sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13307,c_52,c_53,c_54,c_55])).

cnf(c_13775,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK3(sK7,sK8,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_13774])).

cnf(c_13311,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(sK7,X0,X1)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11776,c_11759])).

cnf(c_13780,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_13775,c_13311])).

cnf(c_14395,plain,
    ( v1_compts_1(sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13780,c_52,c_53,c_54,c_55])).

cnf(c_14396,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_14395])).

cnf(c_14402,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11777,c_14396])).

cnf(c_24,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2094,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_41])).

cnf(c_2095,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_2094])).

cnf(c_2099,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2095,c_42,c_40])).

cnf(c_2100,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_2099])).

cnf(c_11875,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2100])).

cnf(c_11876,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11875])).

cnf(c_14523,plain,
    ( v1_compts_1(sK7) != iProver_top
    | k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14402,c_52,c_53,c_54,c_55,c_11876])).

cnf(c_14524,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
    | v1_compts_1(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_14523])).

cnf(c_15966,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15961,c_14524])).

cnf(c_21,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1819,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_41])).

cnf(c_1820,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1819])).

cnf(c_1824,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1820,c_42,c_40])).

cnf(c_1825,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1824])).

cnf(c_11775,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1))) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1825])).

cnf(c_16083,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15966,c_11775])).

cnf(c_11886,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_11887,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11886])).

cnf(c_16152,plain,
    ( r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16083,c_52,c_53,c_54,c_55,c_1670,c_1684,c_1698,c_1712,c_11876,c_11887,c_12244,c_13275,c_15921])).

cnf(c_16156,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_16152,c_12529])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 4.07/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.02  
% 4.07/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/1.02  
% 4.07/1.02  ------  iProver source info
% 4.07/1.02  
% 4.07/1.02  git: date: 2020-06-30 10:37:57 +0100
% 4.07/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/1.02  git: non_committed_changes: false
% 4.07/1.02  git: last_make_outside_of_git: false
% 4.07/1.02  
% 4.07/1.02  ------ 
% 4.07/1.02  
% 4.07/1.02  ------ Input Options
% 4.07/1.02  
% 4.07/1.02  --out_options                           all
% 4.07/1.02  --tptp_safe_out                         true
% 4.07/1.02  --problem_path                          ""
% 4.07/1.02  --include_path                          ""
% 4.07/1.02  --clausifier                            res/vclausify_rel
% 4.07/1.02  --clausifier_options                    ""
% 4.07/1.02  --stdin                                 false
% 4.07/1.02  --stats_out                             all
% 4.07/1.02  
% 4.07/1.02  ------ General Options
% 4.07/1.02  
% 4.07/1.02  --fof                                   false
% 4.07/1.02  --time_out_real                         305.
% 4.07/1.02  --time_out_virtual                      -1.
% 4.07/1.02  --symbol_type_check                     false
% 4.07/1.02  --clausify_out                          false
% 4.07/1.02  --sig_cnt_out                           false
% 4.07/1.02  --trig_cnt_out                          false
% 4.07/1.02  --trig_cnt_out_tolerance                1.
% 4.07/1.02  --trig_cnt_out_sk_spl                   false
% 4.07/1.02  --abstr_cl_out                          false
% 4.07/1.02  
% 4.07/1.02  ------ Global Options
% 4.07/1.02  
% 4.07/1.02  --schedule                              default
% 4.07/1.02  --add_important_lit                     false
% 4.07/1.02  --prop_solver_per_cl                    1000
% 4.07/1.02  --min_unsat_core                        false
% 4.07/1.02  --soft_assumptions                      false
% 4.07/1.02  --soft_lemma_size                       3
% 4.07/1.02  --prop_impl_unit_size                   0
% 4.07/1.02  --prop_impl_unit                        []
% 4.07/1.02  --share_sel_clauses                     true
% 4.07/1.02  --reset_solvers                         false
% 4.07/1.02  --bc_imp_inh                            [conj_cone]
% 4.07/1.02  --conj_cone_tolerance                   3.
% 4.07/1.02  --extra_neg_conj                        none
% 4.07/1.02  --large_theory_mode                     true
% 4.07/1.02  --prolific_symb_bound                   200
% 4.07/1.02  --lt_threshold                          2000
% 4.07/1.02  --clause_weak_htbl                      true
% 4.07/1.02  --gc_record_bc_elim                     false
% 4.07/1.02  
% 4.07/1.02  ------ Preprocessing Options
% 4.07/1.02  
% 4.07/1.02  --preprocessing_flag                    true
% 4.07/1.02  --time_out_prep_mult                    0.1
% 4.07/1.02  --splitting_mode                        input
% 4.07/1.02  --splitting_grd                         true
% 4.07/1.02  --splitting_cvd                         false
% 4.07/1.02  --splitting_cvd_svl                     false
% 4.07/1.02  --splitting_nvd                         32
% 4.07/1.02  --sub_typing                            true
% 4.07/1.02  --prep_gs_sim                           true
% 4.07/1.02  --prep_unflatten                        true
% 4.07/1.02  --prep_res_sim                          true
% 4.07/1.02  --prep_upred                            true
% 4.07/1.02  --prep_sem_filter                       exhaustive
% 4.07/1.02  --prep_sem_filter_out                   false
% 4.07/1.02  --pred_elim                             true
% 4.07/1.02  --res_sim_input                         true
% 4.07/1.02  --eq_ax_congr_red                       true
% 4.07/1.02  --pure_diseq_elim                       true
% 4.07/1.02  --brand_transform                       false
% 4.07/1.02  --non_eq_to_eq                          false
% 4.07/1.02  --prep_def_merge                        true
% 4.07/1.02  --prep_def_merge_prop_impl              false
% 4.07/1.02  --prep_def_merge_mbd                    true
% 4.07/1.02  --prep_def_merge_tr_red                 false
% 4.07/1.02  --prep_def_merge_tr_cl                  false
% 4.07/1.02  --smt_preprocessing                     true
% 4.07/1.02  --smt_ac_axioms                         fast
% 4.07/1.02  --preprocessed_out                      false
% 4.07/1.02  --preprocessed_stats                    false
% 4.07/1.02  
% 4.07/1.02  ------ Abstraction refinement Options
% 4.07/1.02  
% 4.07/1.02  --abstr_ref                             []
% 4.07/1.02  --abstr_ref_prep                        false
% 4.07/1.02  --abstr_ref_until_sat                   false
% 4.07/1.02  --abstr_ref_sig_restrict                funpre
% 4.07/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/1.02  --abstr_ref_under                       []
% 4.07/1.02  
% 4.07/1.02  ------ SAT Options
% 4.07/1.02  
% 4.07/1.02  --sat_mode                              false
% 4.07/1.02  --sat_fm_restart_options                ""
% 4.07/1.02  --sat_gr_def                            false
% 4.07/1.02  --sat_epr_types                         true
% 4.07/1.02  --sat_non_cyclic_types                  false
% 4.07/1.02  --sat_finite_models                     false
% 4.07/1.02  --sat_fm_lemmas                         false
% 4.07/1.02  --sat_fm_prep                           false
% 4.07/1.02  --sat_fm_uc_incr                        true
% 4.07/1.02  --sat_out_model                         small
% 4.07/1.02  --sat_out_clauses                       false
% 4.07/1.02  
% 4.07/1.02  ------ QBF Options
% 4.07/1.02  
% 4.07/1.02  --qbf_mode                              false
% 4.07/1.02  --qbf_elim_univ                         false
% 4.07/1.02  --qbf_dom_inst                          none
% 4.07/1.02  --qbf_dom_pre_inst                      false
% 4.07/1.02  --qbf_sk_in                             false
% 4.07/1.02  --qbf_pred_elim                         true
% 4.07/1.02  --qbf_split                             512
% 4.07/1.02  
% 4.07/1.02  ------ BMC1 Options
% 4.07/1.02  
% 4.07/1.02  --bmc1_incremental                      false
% 4.07/1.02  --bmc1_axioms                           reachable_all
% 4.07/1.02  --bmc1_min_bound                        0
% 4.07/1.02  --bmc1_max_bound                        -1
% 4.07/1.02  --bmc1_max_bound_default                -1
% 4.07/1.02  --bmc1_symbol_reachability              true
% 4.07/1.02  --bmc1_property_lemmas                  false
% 4.07/1.02  --bmc1_k_induction                      false
% 4.07/1.02  --bmc1_non_equiv_states                 false
% 4.07/1.02  --bmc1_deadlock                         false
% 4.07/1.02  --bmc1_ucm                              false
% 4.07/1.02  --bmc1_add_unsat_core                   none
% 4.07/1.02  --bmc1_unsat_core_children              false
% 4.07/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/1.02  --bmc1_out_stat                         full
% 4.07/1.02  --bmc1_ground_init                      false
% 4.07/1.02  --bmc1_pre_inst_next_state              false
% 4.07/1.02  --bmc1_pre_inst_state                   false
% 4.07/1.02  --bmc1_pre_inst_reach_state             false
% 4.07/1.02  --bmc1_out_unsat_core                   false
% 4.07/1.02  --bmc1_aig_witness_out                  false
% 4.07/1.02  --bmc1_verbose                          false
% 4.07/1.02  --bmc1_dump_clauses_tptp                false
% 4.07/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.07/1.02  --bmc1_dump_file                        -
% 4.07/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.07/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.07/1.02  --bmc1_ucm_extend_mode                  1
% 4.07/1.02  --bmc1_ucm_init_mode                    2
% 4.07/1.02  --bmc1_ucm_cone_mode                    none
% 4.07/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.07/1.02  --bmc1_ucm_relax_model                  4
% 4.07/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.07/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/1.02  --bmc1_ucm_layered_model                none
% 4.07/1.02  --bmc1_ucm_max_lemma_size               10
% 4.07/1.02  
% 4.07/1.02  ------ AIG Options
% 4.07/1.02  
% 4.07/1.02  --aig_mode                              false
% 4.07/1.02  
% 4.07/1.02  ------ Instantiation Options
% 4.07/1.02  
% 4.07/1.02  --instantiation_flag                    true
% 4.07/1.02  --inst_sos_flag                         true
% 4.07/1.02  --inst_sos_phase                        true
% 4.07/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/1.02  --inst_lit_sel_side                     num_symb
% 4.07/1.02  --inst_solver_per_active                1400
% 4.07/1.02  --inst_solver_calls_frac                1.
% 4.07/1.02  --inst_passive_queue_type               priority_queues
% 4.07/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/1.02  --inst_passive_queues_freq              [25;2]
% 4.07/1.02  --inst_dismatching                      true
% 4.07/1.02  --inst_eager_unprocessed_to_passive     true
% 4.07/1.02  --inst_prop_sim_given                   true
% 4.07/1.02  --inst_prop_sim_new                     false
% 4.07/1.02  --inst_subs_new                         false
% 4.07/1.02  --inst_eq_res_simp                      false
% 4.07/1.02  --inst_subs_given                       false
% 4.07/1.02  --inst_orphan_elimination               true
% 4.07/1.02  --inst_learning_loop_flag               true
% 4.07/1.02  --inst_learning_start                   3000
% 4.07/1.02  --inst_learning_factor                  2
% 4.07/1.02  --inst_start_prop_sim_after_learn       3
% 4.07/1.02  --inst_sel_renew                        solver
% 4.07/1.02  --inst_lit_activity_flag                true
% 4.07/1.02  --inst_restr_to_given                   false
% 4.07/1.02  --inst_activity_threshold               500
% 4.07/1.02  --inst_out_proof                        true
% 4.07/1.02  
% 4.07/1.02  ------ Resolution Options
% 4.07/1.02  
% 4.07/1.02  --resolution_flag                       true
% 4.07/1.02  --res_lit_sel                           adaptive
% 4.07/1.02  --res_lit_sel_side                      none
% 4.07/1.02  --res_ordering                          kbo
% 4.07/1.02  --res_to_prop_solver                    active
% 4.07/1.02  --res_prop_simpl_new                    false
% 4.07/1.02  --res_prop_simpl_given                  true
% 4.07/1.02  --res_passive_queue_type                priority_queues
% 4.07/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/1.02  --res_passive_queues_freq               [15;5]
% 4.07/1.02  --res_forward_subs                      full
% 4.07/1.02  --res_backward_subs                     full
% 4.07/1.02  --res_forward_subs_resolution           true
% 4.07/1.02  --res_backward_subs_resolution          true
% 4.07/1.02  --res_orphan_elimination                true
% 4.07/1.02  --res_time_limit                        2.
% 4.07/1.02  --res_out_proof                         true
% 4.07/1.02  
% 4.07/1.02  ------ Superposition Options
% 4.07/1.02  
% 4.07/1.02  --superposition_flag                    true
% 4.07/1.02  --sup_passive_queue_type                priority_queues
% 4.07/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.07/1.02  --demod_completeness_check              fast
% 4.07/1.02  --demod_use_ground                      true
% 4.07/1.02  --sup_to_prop_solver                    passive
% 4.07/1.02  --sup_prop_simpl_new                    true
% 4.07/1.02  --sup_prop_simpl_given                  true
% 4.07/1.02  --sup_fun_splitting                     true
% 4.07/1.02  --sup_smt_interval                      50000
% 4.07/1.02  
% 4.07/1.02  ------ Superposition Simplification Setup
% 4.07/1.02  
% 4.07/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/1.02  --sup_immed_triv                        [TrivRules]
% 4.07/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.02  --sup_immed_bw_main                     []
% 4.07/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.02  --sup_input_bw                          []
% 4.07/1.02  
% 4.07/1.02  ------ Combination Options
% 4.07/1.02  
% 4.07/1.02  --comb_res_mult                         3
% 4.07/1.02  --comb_sup_mult                         2
% 4.07/1.02  --comb_inst_mult                        10
% 4.07/1.02  
% 4.07/1.02  ------ Debug Options
% 4.07/1.02  
% 4.07/1.02  --dbg_backtrace                         false
% 4.07/1.02  --dbg_dump_prop_clauses                 false
% 4.07/1.02  --dbg_dump_prop_clauses_file            -
% 4.07/1.02  --dbg_out_stat                          false
% 4.07/1.02  ------ Parsing...
% 4.07/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/1.02  
% 4.07/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.07/1.02  
% 4.07/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/1.02  
% 4.07/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/1.02  ------ Proving...
% 4.07/1.02  ------ Problem Properties 
% 4.07/1.02  
% 4.07/1.02  
% 4.07/1.02  clauses                                 37
% 4.07/1.02  conjectures                             6
% 4.07/1.02  EPR                                     9
% 4.07/1.02  Horn                                    11
% 4.07/1.02  unary                                   2
% 4.07/1.02  binary                                  10
% 4.07/1.02  lits                                    185
% 4.07/1.02  lits eq                                 6
% 4.07/1.02  fd_pure                                 0
% 4.07/1.02  fd_pseudo                               0
% 4.07/1.02  fd_cond                                 0
% 4.07/1.02  fd_pseudo_cond                          4
% 4.07/1.02  AC symbols                              0
% 4.07/1.02  
% 4.07/1.02  ------ Schedule dynamic 5 is on 
% 4.07/1.02  
% 4.07/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/1.02  
% 4.07/1.02  
% 4.07/1.02  ------ 
% 4.07/1.02  Current options:
% 4.07/1.02  ------ 
% 4.07/1.02  
% 4.07/1.02  ------ Input Options
% 4.07/1.02  
% 4.07/1.02  --out_options                           all
% 4.07/1.02  --tptp_safe_out                         true
% 4.07/1.02  --problem_path                          ""
% 4.07/1.02  --include_path                          ""
% 4.07/1.02  --clausifier                            res/vclausify_rel
% 4.07/1.02  --clausifier_options                    ""
% 4.07/1.02  --stdin                                 false
% 4.07/1.02  --stats_out                             all
% 4.07/1.02  
% 4.07/1.02  ------ General Options
% 4.07/1.02  
% 4.07/1.02  --fof                                   false
% 4.07/1.02  --time_out_real                         305.
% 4.07/1.02  --time_out_virtual                      -1.
% 4.07/1.02  --symbol_type_check                     false
% 4.07/1.02  --clausify_out                          false
% 4.07/1.02  --sig_cnt_out                           false
% 4.07/1.02  --trig_cnt_out                          false
% 4.07/1.02  --trig_cnt_out_tolerance                1.
% 4.07/1.02  --trig_cnt_out_sk_spl                   false
% 4.07/1.02  --abstr_cl_out                          false
% 4.07/1.02  
% 4.07/1.02  ------ Global Options
% 4.07/1.02  
% 4.07/1.02  --schedule                              default
% 4.07/1.02  --add_important_lit                     false
% 4.07/1.02  --prop_solver_per_cl                    1000
% 4.07/1.02  --min_unsat_core                        false
% 4.07/1.02  --soft_assumptions                      false
% 4.07/1.02  --soft_lemma_size                       3
% 4.07/1.02  --prop_impl_unit_size                   0
% 4.07/1.02  --prop_impl_unit                        []
% 4.07/1.02  --share_sel_clauses                     true
% 4.07/1.02  --reset_solvers                         false
% 4.07/1.02  --bc_imp_inh                            [conj_cone]
% 4.07/1.02  --conj_cone_tolerance                   3.
% 4.07/1.02  --extra_neg_conj                        none
% 4.07/1.02  --large_theory_mode                     true
% 4.07/1.02  --prolific_symb_bound                   200
% 4.07/1.02  --lt_threshold                          2000
% 4.07/1.02  --clause_weak_htbl                      true
% 4.07/1.02  --gc_record_bc_elim                     false
% 4.07/1.02  
% 4.07/1.02  ------ Preprocessing Options
% 4.07/1.02  
% 4.07/1.02  --preprocessing_flag                    true
% 4.07/1.02  --time_out_prep_mult                    0.1
% 4.07/1.02  --splitting_mode                        input
% 4.07/1.02  --splitting_grd                         true
% 4.07/1.02  --splitting_cvd                         false
% 4.07/1.02  --splitting_cvd_svl                     false
% 4.07/1.02  --splitting_nvd                         32
% 4.07/1.02  --sub_typing                            true
% 4.07/1.02  --prep_gs_sim                           true
% 4.07/1.02  --prep_unflatten                        true
% 4.07/1.02  --prep_res_sim                          true
% 4.07/1.02  --prep_upred                            true
% 4.07/1.02  --prep_sem_filter                       exhaustive
% 4.07/1.02  --prep_sem_filter_out                   false
% 4.07/1.02  --pred_elim                             true
% 4.07/1.02  --res_sim_input                         true
% 4.07/1.02  --eq_ax_congr_red                       true
% 4.07/1.02  --pure_diseq_elim                       true
% 4.07/1.02  --brand_transform                       false
% 4.07/1.02  --non_eq_to_eq                          false
% 4.07/1.02  --prep_def_merge                        true
% 4.07/1.02  --prep_def_merge_prop_impl              false
% 4.07/1.02  --prep_def_merge_mbd                    true
% 4.07/1.02  --prep_def_merge_tr_red                 false
% 4.07/1.02  --prep_def_merge_tr_cl                  false
% 4.07/1.02  --smt_preprocessing                     true
% 4.07/1.02  --smt_ac_axioms                         fast
% 4.07/1.02  --preprocessed_out                      false
% 4.07/1.02  --preprocessed_stats                    false
% 4.07/1.02  
% 4.07/1.02  ------ Abstraction refinement Options
% 4.07/1.02  
% 4.07/1.02  --abstr_ref                             []
% 4.07/1.02  --abstr_ref_prep                        false
% 4.07/1.02  --abstr_ref_until_sat                   false
% 4.07/1.02  --abstr_ref_sig_restrict                funpre
% 4.07/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/1.02  --abstr_ref_under                       []
% 4.07/1.02  
% 4.07/1.02  ------ SAT Options
% 4.07/1.02  
% 4.07/1.02  --sat_mode                              false
% 4.07/1.02  --sat_fm_restart_options                ""
% 4.07/1.02  --sat_gr_def                            false
% 4.07/1.02  --sat_epr_types                         true
% 4.07/1.02  --sat_non_cyclic_types                  false
% 4.07/1.02  --sat_finite_models                     false
% 4.07/1.02  --sat_fm_lemmas                         false
% 4.07/1.02  --sat_fm_prep                           false
% 4.07/1.02  --sat_fm_uc_incr                        true
% 4.07/1.02  --sat_out_model                         small
% 4.07/1.02  --sat_out_clauses                       false
% 4.07/1.02  
% 4.07/1.02  ------ QBF Options
% 4.07/1.02  
% 4.07/1.02  --qbf_mode                              false
% 4.07/1.02  --qbf_elim_univ                         false
% 4.07/1.02  --qbf_dom_inst                          none
% 4.07/1.02  --qbf_dom_pre_inst                      false
% 4.07/1.02  --qbf_sk_in                             false
% 4.07/1.02  --qbf_pred_elim                         true
% 4.07/1.02  --qbf_split                             512
% 4.07/1.02  
% 4.07/1.02  ------ BMC1 Options
% 4.07/1.02  
% 4.07/1.02  --bmc1_incremental                      false
% 4.07/1.02  --bmc1_axioms                           reachable_all
% 4.07/1.02  --bmc1_min_bound                        0
% 4.07/1.02  --bmc1_max_bound                        -1
% 4.07/1.02  --bmc1_max_bound_default                -1
% 4.07/1.02  --bmc1_symbol_reachability              true
% 4.07/1.02  --bmc1_property_lemmas                  false
% 4.07/1.02  --bmc1_k_induction                      false
% 4.07/1.02  --bmc1_non_equiv_states                 false
% 4.07/1.02  --bmc1_deadlock                         false
% 4.07/1.02  --bmc1_ucm                              false
% 4.07/1.02  --bmc1_add_unsat_core                   none
% 4.07/1.02  --bmc1_unsat_core_children              false
% 4.07/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/1.02  --bmc1_out_stat                         full
% 4.07/1.02  --bmc1_ground_init                      false
% 4.07/1.02  --bmc1_pre_inst_next_state              false
% 4.07/1.02  --bmc1_pre_inst_state                   false
% 4.07/1.02  --bmc1_pre_inst_reach_state             false
% 4.07/1.02  --bmc1_out_unsat_core                   false
% 4.07/1.02  --bmc1_aig_witness_out                  false
% 4.07/1.02  --bmc1_verbose                          false
% 4.07/1.02  --bmc1_dump_clauses_tptp                false
% 4.07/1.02  --bmc1_dump_unsat_core_tptp             false
% 4.07/1.02  --bmc1_dump_file                        -
% 4.07/1.02  --bmc1_ucm_expand_uc_limit              128
% 4.07/1.02  --bmc1_ucm_n_expand_iterations          6
% 4.07/1.02  --bmc1_ucm_extend_mode                  1
% 4.07/1.02  --bmc1_ucm_init_mode                    2
% 4.07/1.02  --bmc1_ucm_cone_mode                    none
% 4.07/1.02  --bmc1_ucm_reduced_relation_type        0
% 4.07/1.02  --bmc1_ucm_relax_model                  4
% 4.07/1.02  --bmc1_ucm_full_tr_after_sat            true
% 4.07/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/1.02  --bmc1_ucm_layered_model                none
% 4.07/1.02  --bmc1_ucm_max_lemma_size               10
% 4.07/1.02  
% 4.07/1.02  ------ AIG Options
% 4.07/1.02  
% 4.07/1.02  --aig_mode                              false
% 4.07/1.02  
% 4.07/1.02  ------ Instantiation Options
% 4.07/1.02  
% 4.07/1.02  --instantiation_flag                    true
% 4.07/1.02  --inst_sos_flag                         true
% 4.07/1.02  --inst_sos_phase                        true
% 4.07/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/1.02  --inst_lit_sel_side                     none
% 4.07/1.02  --inst_solver_per_active                1400
% 4.07/1.02  --inst_solver_calls_frac                1.
% 4.07/1.02  --inst_passive_queue_type               priority_queues
% 4.07/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/1.02  --inst_passive_queues_freq              [25;2]
% 4.07/1.02  --inst_dismatching                      true
% 4.07/1.02  --inst_eager_unprocessed_to_passive     true
% 4.07/1.02  --inst_prop_sim_given                   true
% 4.07/1.02  --inst_prop_sim_new                     false
% 4.07/1.02  --inst_subs_new                         false
% 4.07/1.02  --inst_eq_res_simp                      false
% 4.07/1.02  --inst_subs_given                       false
% 4.07/1.02  --inst_orphan_elimination               true
% 4.07/1.02  --inst_learning_loop_flag               true
% 4.07/1.02  --inst_learning_start                   3000
% 4.07/1.02  --inst_learning_factor                  2
% 4.07/1.02  --inst_start_prop_sim_after_learn       3
% 4.07/1.02  --inst_sel_renew                        solver
% 4.07/1.02  --inst_lit_activity_flag                true
% 4.07/1.02  --inst_restr_to_given                   false
% 4.07/1.02  --inst_activity_threshold               500
% 4.07/1.02  --inst_out_proof                        true
% 4.07/1.02  
% 4.07/1.02  ------ Resolution Options
% 4.07/1.02  
% 4.07/1.02  --resolution_flag                       false
% 4.07/1.02  --res_lit_sel                           adaptive
% 4.07/1.02  --res_lit_sel_side                      none
% 4.07/1.02  --res_ordering                          kbo
% 4.07/1.02  --res_to_prop_solver                    active
% 4.07/1.02  --res_prop_simpl_new                    false
% 4.07/1.02  --res_prop_simpl_given                  true
% 4.07/1.02  --res_passive_queue_type                priority_queues
% 4.07/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/1.02  --res_passive_queues_freq               [15;5]
% 4.07/1.02  --res_forward_subs                      full
% 4.07/1.02  --res_backward_subs                     full
% 4.07/1.02  --res_forward_subs_resolution           true
% 4.07/1.02  --res_backward_subs_resolution          true
% 4.07/1.02  --res_orphan_elimination                true
% 4.07/1.02  --res_time_limit                        2.
% 4.07/1.02  --res_out_proof                         true
% 4.07/1.02  
% 4.07/1.02  ------ Superposition Options
% 4.07/1.02  
% 4.07/1.02  --superposition_flag                    true
% 4.07/1.02  --sup_passive_queue_type                priority_queues
% 4.07/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/1.02  --sup_passive_queues_freq               [8;1;4]
% 4.07/1.02  --demod_completeness_check              fast
% 4.07/1.02  --demod_use_ground                      true
% 4.07/1.02  --sup_to_prop_solver                    passive
% 4.07/1.02  --sup_prop_simpl_new                    true
% 4.07/1.02  --sup_prop_simpl_given                  true
% 4.07/1.02  --sup_fun_splitting                     true
% 4.07/1.02  --sup_smt_interval                      50000
% 4.07/1.02  
% 4.07/1.02  ------ Superposition Simplification Setup
% 4.07/1.02  
% 4.07/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.07/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.07/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.07/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.07/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.07/1.02  --sup_immed_triv                        [TrivRules]
% 4.07/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.02  --sup_immed_bw_main                     []
% 4.07/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.07/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.02  --sup_input_bw                          []
% 4.07/1.02  
% 4.07/1.02  ------ Combination Options
% 4.07/1.02  
% 4.07/1.02  --comb_res_mult                         3
% 4.07/1.02  --comb_sup_mult                         2
% 4.07/1.02  --comb_inst_mult                        10
% 4.07/1.02  
% 4.07/1.02  ------ Debug Options
% 4.07/1.02  
% 4.07/1.02  --dbg_backtrace                         false
% 4.07/1.02  --dbg_dump_prop_clauses                 false
% 4.07/1.02  --dbg_dump_prop_clauses_file            -
% 4.07/1.02  --dbg_out_stat                          false
% 4.07/1.02  
% 4.07/1.02  
% 4.07/1.02  
% 4.07/1.02  
% 4.07/1.02  ------ Proving...
% 4.07/1.02  
% 4.07/1.02  
% 4.07/1.02  % SZS status Theorem for theBenchmark.p
% 4.07/1.02  
% 4.07/1.02   Resolution empty clause
% 4.07/1.02  
% 4.07/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/1.02  
% 4.07/1.02  fof(f15,conjecture,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f16,negated_conjecture,(
% 4.07/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 4.07/1.02    inference(negated_conjecture,[],[f15])).
% 4.07/1.02  
% 4.07/1.02  fof(f41,plain,(
% 4.07/1.02    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f16])).
% 4.07/1.02  
% 4.07/1.02  fof(f42,plain,(
% 4.07/1.02    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f41])).
% 4.07/1.02  
% 4.07/1.02  fof(f60,plain,(
% 4.07/1.02    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.07/1.02    inference(nnf_transformation,[],[f42])).
% 4.07/1.02  
% 4.07/1.02  fof(f61,plain,(
% 4.07/1.02    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f60])).
% 4.07/1.02  
% 4.07/1.02  fof(f62,plain,(
% 4.07/1.02    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 4.07/1.02    inference(rectify,[],[f61])).
% 4.07/1.02  
% 4.07/1.02  fof(f65,plain,(
% 4.07/1.02    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK9(X3),X0) & m2_yellow_6(sK9(X3),X0,X3)))) )),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f64,plain,(
% 4.07/1.02    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK8)) & l1_waybel_0(sK8,X0) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8))) )),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f63,plain,(
% 4.07/1.02    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,X1)) & l1_waybel_0(X1,sK7) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK7)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK7) & m2_yellow_6(X4,sK7,X3)) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7))),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f66,plain,(
% 4.07/1.02    ((! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,sK8)) & l1_waybel_0(sK8,sK7) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8)) | ~v1_compts_1(sK7)) & (! [X3] : ((v3_yellow_6(sK9(X3),sK7) & m2_yellow_6(sK9(X3),sK7,X3)) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7)),
% 4.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f62,f65,f64,f63])).
% 4.07/1.02  
% 4.07/1.02  fof(f103,plain,(
% 4.07/1.02    ( ! [X3] : (m2_yellow_6(sK9(X3),sK7,X3) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK7)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f7,axiom,(
% 4.07/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f25,plain,(
% 4.07/1.02    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f7])).
% 4.07/1.02  
% 4.07/1.02  fof(f26,plain,(
% 4.07/1.02    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f25])).
% 4.07/1.02  
% 4.07/1.02  fof(f79,plain,(
% 4.07/1.02    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f26])).
% 4.07/1.02  
% 4.07/1.02  fof(f101,plain,(
% 4.07/1.02    v2_pre_topc(sK7)),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f100,plain,(
% 4.07/1.02    ~v2_struct_0(sK7)),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f102,plain,(
% 4.07/1.02    l1_pre_topc(sK7)),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f6,axiom,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f23,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f6])).
% 4.07/1.02  
% 4.07/1.02  fof(f24,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f23])).
% 4.07/1.02  
% 4.07/1.02  fof(f43,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(nnf_transformation,[],[f24])).
% 4.07/1.02  
% 4.07/1.02  fof(f44,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f43])).
% 4.07/1.02  
% 4.07/1.02  fof(f45,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(rectify,[],[f44])).
% 4.07/1.02  
% 4.07/1.02  fof(f48,plain,(
% 4.07/1.02    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6)))),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f47,plain,(
% 4.07/1.02    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X3)))) )),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f46,plain,(
% 4.07/1.02    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f49,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).
% 4.07/1.02  
% 4.07/1.02  fof(f73,plain,(
% 4.07/1.02    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f49])).
% 4.07/1.02  
% 4.07/1.02  fof(f111,plain,(
% 4.07/1.02    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(equality_resolution,[],[f73])).
% 4.07/1.02  
% 4.07/1.02  fof(f76,plain,(
% 4.07/1.02    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2)) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f49])).
% 4.07/1.02  
% 4.07/1.02  fof(f75,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f49])).
% 4.07/1.02  
% 4.07/1.02  fof(f74,plain,(
% 4.07/1.02    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f49])).
% 4.07/1.02  
% 4.07/1.02  fof(f110,plain,(
% 4.07/1.02    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(equality_resolution,[],[f74])).
% 4.07/1.02  
% 4.07/1.02  fof(f1,axiom,(
% 4.07/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f67,plain,(
% 4.07/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.07/1.02    inference(cnf_transformation,[],[f1])).
% 4.07/1.02  
% 4.07/1.02  fof(f2,axiom,(
% 4.07/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f17,plain,(
% 4.07/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 4.07/1.02    inference(unused_predicate_definition_removal,[],[f2])).
% 4.07/1.02  
% 4.07/1.02  fof(f18,plain,(
% 4.07/1.02    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 4.07/1.02    inference(ennf_transformation,[],[f17])).
% 4.07/1.02  
% 4.07/1.02  fof(f68,plain,(
% 4.07/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.07/1.02    inference(cnf_transformation,[],[f18])).
% 4.07/1.02  
% 4.07/1.02  fof(f4,axiom,(
% 4.07/1.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f21,plain,(
% 4.07/1.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.07/1.02    inference(ennf_transformation,[],[f4])).
% 4.07/1.02  
% 4.07/1.02  fof(f70,plain,(
% 4.07/1.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f21])).
% 4.07/1.02  
% 4.07/1.02  fof(f3,axiom,(
% 4.07/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f19,plain,(
% 4.07/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 4.07/1.02    inference(ennf_transformation,[],[f3])).
% 4.07/1.02  
% 4.07/1.02  fof(f20,plain,(
% 4.07/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 4.07/1.02    inference(flattening,[],[f19])).
% 4.07/1.02  
% 4.07/1.02  fof(f69,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f20])).
% 4.07/1.02  
% 4.07/1.02  fof(f10,axiom,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f31,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f10])).
% 4.07/1.02  
% 4.07/1.02  fof(f32,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f31])).
% 4.07/1.02  
% 4.07/1.02  fof(f86,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f32])).
% 4.07/1.02  
% 4.07/1.02  fof(f11,axiom,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f33,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f11])).
% 4.07/1.02  
% 4.07/1.02  fof(f34,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f33])).
% 4.07/1.02  
% 4.07/1.02  fof(f87,plain,(
% 4.07/1.02    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f34])).
% 4.07/1.02  
% 4.07/1.02  fof(f5,axiom,(
% 4.07/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f22,plain,(
% 4.07/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.07/1.02    inference(ennf_transformation,[],[f5])).
% 4.07/1.02  
% 4.07/1.02  fof(f71,plain,(
% 4.07/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f22])).
% 4.07/1.02  
% 4.07/1.02  fof(f8,axiom,(
% 4.07/1.02    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f27,plain,(
% 4.07/1.02    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f8])).
% 4.07/1.02  
% 4.07/1.02  fof(f28,plain,(
% 4.07/1.02    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f27])).
% 4.07/1.02  
% 4.07/1.02  fof(f83,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f28])).
% 4.07/1.02  
% 4.07/1.02  fof(f82,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f28])).
% 4.07/1.02  
% 4.07/1.02  fof(f81,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f28])).
% 4.07/1.02  
% 4.07/1.02  fof(f80,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f28])).
% 4.07/1.02  
% 4.07/1.02  fof(f14,axiom,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f39,plain,(
% 4.07/1.02    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f14])).
% 4.07/1.02  
% 4.07/1.02  fof(f40,plain,(
% 4.07/1.02    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f39])).
% 4.07/1.02  
% 4.07/1.02  fof(f55,plain,(
% 4.07/1.02    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(nnf_transformation,[],[f40])).
% 4.07/1.02  
% 4.07/1.02  fof(f56,plain,(
% 4.07/1.02    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(rectify,[],[f55])).
% 4.07/1.02  
% 4.07/1.02  fof(f58,plain,(
% 4.07/1.02    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))))),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f57,plain,(
% 4.07/1.02    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK5(X0),k6_yellow_6(X0)) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0))))),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f59,plain,(
% 4.07/1.02    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK5(X0),k6_yellow_6(X0)) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f56,f58,f57])).
% 4.07/1.02  
% 4.07/1.02  fof(f99,plain,(
% 4.07/1.02    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f59])).
% 4.07/1.02  
% 4.07/1.02  fof(f94,plain,(
% 4.07/1.02    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f59])).
% 4.07/1.02  
% 4.07/1.02  fof(f95,plain,(
% 4.07/1.02    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f59])).
% 4.07/1.02  
% 4.07/1.02  fof(f96,plain,(
% 4.07/1.02    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f59])).
% 4.07/1.02  
% 4.07/1.02  fof(f97,plain,(
% 4.07/1.02    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK5(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f59])).
% 4.07/1.02  
% 4.07/1.02  fof(f9,axiom,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f29,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f9])).
% 4.07/1.02  
% 4.07/1.02  fof(f30,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f29])).
% 4.07/1.02  
% 4.07/1.02  fof(f50,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(nnf_transformation,[],[f30])).
% 4.07/1.02  
% 4.07/1.02  fof(f84,plain,(
% 4.07/1.02    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f50])).
% 4.07/1.02  
% 4.07/1.02  fof(f104,plain,(
% 4.07/1.02    ( ! [X3] : (v3_yellow_6(sK9(X3),sK7) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK7)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f13,axiom,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f37,plain,(
% 4.07/1.02    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f13])).
% 4.07/1.02  
% 4.07/1.02  fof(f38,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f37])).
% 4.07/1.02  
% 4.07/1.02  fof(f53,plain,(
% 4.07/1.02    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f54,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f53])).
% 4.07/1.02  
% 4.07/1.02  fof(f91,plain,(
% 4.07/1.02    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f54])).
% 4.07/1.02  
% 4.07/1.02  fof(f12,axiom,(
% 4.07/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 4.07/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.02  
% 4.07/1.02  fof(f35,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 4.07/1.02    inference(ennf_transformation,[],[f12])).
% 4.07/1.02  
% 4.07/1.02  fof(f36,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(flattening,[],[f35])).
% 4.07/1.02  
% 4.07/1.02  fof(f51,plain,(
% 4.07/1.02    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)))),
% 4.07/1.02    introduced(choice_axiom,[])).
% 4.07/1.02  
% 4.07/1.02  fof(f52,plain,(
% 4.07/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 4.07/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f51])).
% 4.07/1.02  
% 4.07/1.02  fof(f88,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (m2_yellow_6(sK3(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f52])).
% 4.07/1.02  
% 4.07/1.02  fof(f85,plain,(
% 4.07/1.02    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f50])).
% 4.07/1.02  
% 4.07/1.02  fof(f109,plain,(
% 4.07/1.02    ( ! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,sK8) | ~v1_compts_1(sK7)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f105,plain,(
% 4.07/1.02    ~v2_struct_0(sK8) | ~v1_compts_1(sK7)),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f106,plain,(
% 4.07/1.02    v4_orders_2(sK8) | ~v1_compts_1(sK7)),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f107,plain,(
% 4.07/1.02    v7_waybel_0(sK8) | ~v1_compts_1(sK7)),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f108,plain,(
% 4.07/1.02    l1_waybel_0(sK8,sK7) | ~v1_compts_1(sK7)),
% 4.07/1.02    inference(cnf_transformation,[],[f66])).
% 4.07/1.02  
% 4.07/1.02  fof(f90,plain,(
% 4.07/1.02    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f54])).
% 4.07/1.02  
% 4.07/1.02  fof(f89,plain,(
% 4.07/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 4.07/1.02    inference(cnf_transformation,[],[f52])).
% 4.07/1.02  
% 4.07/1.02  cnf(c_39,negated_conjecture,
% 4.07/1.02      ( m2_yellow_6(sK9(X0),sK7,X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f103]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11789,plain,
% 4.07/1.02      ( m2_yellow_6(sK9(X0),sK7,X0) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.02      | ~ v2_pre_topc(X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X1) ),
% 4.07/1.02      inference(cnf_transformation,[],[f79]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_41,negated_conjecture,
% 4.07/1.02      ( v2_pre_topc(sK7) ),
% 4.07/1.02      inference(cnf_transformation,[],[f101]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2124,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2125,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2124]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_42,negated_conjecture,
% 4.07/1.02      ( ~ v2_struct_0(sK7) ),
% 4.07/1.02      inference(cnf_transformation,[],[f100]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_40,negated_conjecture,
% 4.07/1.02      ( l1_pre_topc(sK7) ),
% 4.07/1.02      inference(cnf_transformation,[],[f102]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2129,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_2125,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2130,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_2129]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_10,plain,
% 4.07/1.02      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f111]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1917,plain,
% 4.07/1.02      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1918,plain,
% 4.07/1.02      ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1917]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1922,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1918,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1923,plain,
% 4.07/1.02      ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1922]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2147,plain,
% 4.07/1.02      ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_2130,c_1923]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11767,plain,
% 4.07/1.02      ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2147]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_7,plain,
% 4.07/1.02      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 4.07/1.02      | r1_waybel_0(X1,X2,X0)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | r2_hidden(sK0(X1,X2,X3),X3)
% 4.07/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.02      | ~ v2_pre_topc(X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | k10_yellow_6(X1,X2) = X3 ),
% 4.07/1.02      inference(cnf_transformation,[],[f76]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2232,plain,
% 4.07/1.02      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 4.07/1.02      | r1_waybel_0(X1,X2,X0)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | r2_hidden(sK0(X1,X2,X3),X3)
% 4.07/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | k10_yellow_6(X1,X2) = X3
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2233,plain,
% 4.07/1.02      ( ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
% 4.07/1.02      | r1_waybel_0(sK7,X1,X0)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | r2_hidden(sK0(sK7,X1,X2),X2)
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(sK7)
% 4.07/1.02      | k10_yellow_6(sK7,X1) = X2 ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2232]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2237,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
% 4.07/1.02      | r1_waybel_0(sK7,X1,X0)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | r2_hidden(sK0(sK7,X1,X2),X2)
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | k10_yellow_6(sK7,X1) = X2 ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_2233,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2238,plain,
% 4.07/1.02      ( ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
% 4.07/1.02      | r1_waybel_0(sK7,X1,X0)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | r2_hidden(sK0(sK7,X1,X2),X2)
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | k10_yellow_6(sK7,X1) = X2 ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_2237]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11763,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | m1_connsp_2(X2,sK7,sK0(sK7,X0,X1)) != iProver_top
% 4.07/1.02      | r1_waybel_0(sK7,X0,X2) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2238]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_13749,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
% 4.07/1.02      | l1_waybel_0(X2,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X2) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X2) != iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X2) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_11767,c_11763]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2761,plain,
% 4.07/1.02      ( r1_waybel_0(sK7,X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X3,k10_yellow_6(sK7,X2))
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X4),X4)
% 4.07/1.02      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 4.07/1.02      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | sK2(sK7,X2,X3) != X1
% 4.07/1.02      | sK0(sK7,X0,X4) != X3
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X4
% 4.07/1.02      | sK7 != sK7 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_2147,c_2238]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2762,plain,
% 4.07/1.02      ( r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,X2)))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X2),X2)
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X2),k10_yellow_6(sK7,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | ~ m1_subset_1(sK0(sK7,X0,X2),u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X2 ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2761]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_8,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.02      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 4.07/1.02      | ~ v2_pre_topc(X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | k10_yellow_6(X1,X0) = X2 ),
% 4.07/1.02      inference(cnf_transformation,[],[f75]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2199,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.02      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | k10_yellow_6(X1,X0) = X2
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2200,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7)
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X1 ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2199]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2204,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X1 ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_2200,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2205,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X1 ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_2204]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2794,plain,
% 4.07/1.02      ( r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,X2)))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X2),X2)
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X2),k10_yellow_6(sK7,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X2 ),
% 4.07/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_2762,c_2205]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2808,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X2,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(X2) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v4_orders_2(X2) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X2) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2794]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14152,plain,
% 4.07/1.02      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X2,sK7) != iProver_top
% 4.07/1.02      | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | v2_struct_0(X2) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X2) != iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X2) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_13749,c_2808]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14153,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | r1_waybel_0(sK7,X0,sK2(sK7,X2,sK0(sK7,X0,X1))) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X2,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(X2) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v4_orders_2(X2) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X2) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_14152]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_9,plain,
% 4.07/1.02      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f110]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1953,plain,
% 4.07/1.02      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1954,plain,
% 4.07/1.02      ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1953]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1958,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1954,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1959,plain,
% 4.07/1.02      ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1958]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2148,plain,
% 4.07/1.02      ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_2130,c_1959]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11766,plain,
% 4.07/1.02      ( r1_waybel_0(sK7,X0,sK2(sK7,X0,X1)) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2148]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14160,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_14153,c_11766]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_43,plain,
% 4.07/1.02      ( v2_struct_0(sK7) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_45,plain,
% 4.07/1.02      ( l1_pre_topc(sK7) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2201,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(sK7) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | l1_pre_topc(sK7) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2200]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15575,plain,
% 4.07/1.02      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_14160,c_43,c_45,c_2201]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15576,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),X1) = iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,X1),k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_15575]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_0,plain,
% 4.07/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.07/1.02      inference(cnf_transformation,[],[f67]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11795,plain,
% 4.07/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1,plain,
% 4.07/1.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.07/1.02      inference(cnf_transformation,[],[f68]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_3,plain,
% 4.07/1.02      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f70]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_475,plain,
% 4.07/1.02      ( ~ r2_hidden(X0,X1)
% 4.07/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 4.07/1.02      | X1 != X2
% 4.07/1.02      | X0 != X3 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_476,plain,
% 4.07/1.02      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_475]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11787,plain,
% 4.07/1.02      ( r2_hidden(X0,X1) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12529,plain,
% 4.07/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_11795,c_11787]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15588,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_15576,c_12529]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12315,plain,
% 4.07/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 4.07/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12316,plain,
% 4.07/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_12315]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15616,plain,
% 4.07/1.02      ( r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_15588,c_12316]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15617,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_15616]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11768,plain,
% 4.07/1.02      ( l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2130]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2,plain,
% 4.07/1.02      ( ~ r2_hidden(X0,X1)
% 4.07/1.02      | m1_subset_1(X0,X2)
% 4.07/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 4.07/1.02      inference(cnf_transformation,[],[f69]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11794,plain,
% 4.07/1.02      ( r2_hidden(X0,X1) != iProver_top
% 4.07/1.02      | m1_subset_1(X0,X2) = iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12293,plain,
% 4.07/1.02      ( l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,u1_struct_0(sK7)) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_11768,c_11794]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15624,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_15617,c_12293]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11764,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = X1
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2205]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14159,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,k1_xboole_0))) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X1)) = iProver_top
% 4.07/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_14153,c_12529]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14414,plain,
% 4.07/1.02      ( r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X1)) = iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,k1_xboole_0))) = iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_14159,c_12316]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14415,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r1_waybel_0(sK7,X0,sK2(sK7,X1,sK0(sK7,X0,k1_xboole_0))) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X1)) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_14414]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14420,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(sK0(sK7,X0,k1_xboole_0),k10_yellow_6(sK7,X0)) = iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_14415,c_11766]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_19,plain,
% 4.07/1.02      ( r3_waybel_9(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f86]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1884,plain,
% 4.07/1.02      ( r3_waybel_9(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1885,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1884]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1889,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1885,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1890,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1889]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11773,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,X1) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1891,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,X1) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12947,plain,
% 4.07/1.02      ( r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r3_waybel_9(sK7,X0,X1) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_11773,c_1891,c_12293]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12948,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,X1) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_12947]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14528,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_14420,c_12948]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14637,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_11764,c_14528]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14647,plain,
% 4.07/1.02      ( l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_14637,c_12316]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14648,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r3_waybel_9(sK7,X0,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_14647]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_20,plain,
% 4.07/1.02      ( ~ r3_waybel_9(X0,X1,X2)
% 4.07/1.02      | r3_waybel_9(X0,X3,X2)
% 4.07/1.02      | ~ m2_yellow_6(X1,X0,X3)
% 4.07/1.02      | ~ l1_waybel_0(X3,X0)
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X3)
% 4.07/1.02      | ~ v4_orders_2(X3)
% 4.07/1.02      | ~ v7_waybel_0(X3)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f87]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1852,plain,
% 4.07/1.02      ( ~ r3_waybel_9(X0,X1,X2)
% 4.07/1.02      | r3_waybel_9(X0,X3,X2)
% 4.07/1.02      | ~ m2_yellow_6(X1,X0,X3)
% 4.07/1.02      | ~ l1_waybel_0(X3,X0)
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X3)
% 4.07/1.02      | ~ v4_orders_2(X3)
% 4.07/1.02      | ~ v7_waybel_0(X3)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1853,plain,
% 4.07/1.02      ( ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | r3_waybel_9(sK7,X2,X1)
% 4.07/1.02      | ~ m2_yellow_6(X0,sK7,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1852]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1855,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | r3_waybel_9(sK7,X2,X1)
% 4.07/1.02      | ~ m2_yellow_6(X0,sK7,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X2) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1853,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1856,plain,
% 4.07/1.02      ( ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | r3_waybel_9(sK7,X2,X1)
% 4.07/1.02      | ~ m2_yellow_6(X0,sK7,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1855]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11774,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 4.07/1.02      | r3_waybel_9(sK7,X2,X1) = iProver_top
% 4.07/1.02      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 4.07/1.02      | l1_waybel_0(X2,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X2) = iProver_top
% 4.07/1.02      | v4_orders_2(X2) != iProver_top
% 4.07/1.02      | v7_waybel_0(X2) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1856]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15630,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) != iProver_top
% 4.07/1.02      | r3_waybel_9(sK7,X2,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | m2_yellow_6(X1,sK7,X2) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X2,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(X2) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v4_orders_2(X2) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X2) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_15624,c_11774]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15747,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_14648,c_15630]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_4,plain,
% 4.07/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f71]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_13,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | l1_waybel_0(X0,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_struct_0(X1) ),
% 4.07/1.02      inference(cnf_transformation,[],[f83]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_574,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | l1_waybel_0(X0,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X3)
% 4.07/1.02      | X1 != X3 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_575,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | l1_waybel_0(X0,X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X1) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_574]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2420,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | l1_waybel_0(X0,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_575,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2421,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | l1_waybel_0(X0,sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2420]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2423,plain,
% 4.07/1.02      ( v2_struct_0(X1)
% 4.07/1.02      | l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2421,c_42]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2424,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | l1_waybel_0(X0,sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_2423]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2425,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2424]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_14,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_struct_0(X1) ),
% 4.07/1.02      inference(cnf_transformation,[],[f82]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_546,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X3)
% 4.07/1.02      | X1 != X3 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_547,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X1) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_546]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2446,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | v7_waybel_0(X0)
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_547,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2447,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | v7_waybel_0(X0) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2446]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2449,plain,
% 4.07/1.02      ( v2_struct_0(X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | v7_waybel_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2447,c_42]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2450,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_2449]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2451,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2450]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_struct_0(X1) ),
% 4.07/1.02      inference(cnf_transformation,[],[f81]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_518,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X3)
% 4.07/1.02      | X1 != X3 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_519,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X1) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_518]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2472,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_519,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2473,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2472]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2475,plain,
% 4.07/1.02      ( v2_struct_0(X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2473,c_42]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2476,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_2475]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2477,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v4_orders_2(X0) = iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2476]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_16,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | ~ v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_struct_0(X1) ),
% 4.07/1.02      inference(cnf_transformation,[],[f80]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_490,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | ~ v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X3)
% 4.07/1.02      | X1 != X3 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_491,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | ~ v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X1) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_490]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2498,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,X1,X2)
% 4.07/1.02      | ~ l1_waybel_0(X2,X1)
% 4.07/1.02      | ~ v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_491,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2499,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | ~ v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_2498]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2501,plain,
% 4.07/1.02      ( v2_struct_0(X1)
% 4.07/1.02      | ~ v2_struct_0(X0)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2499,c_42]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2502,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,sK7)
% 4.07/1.02      | ~ v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_2501]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_2503,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) != iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15824,plain,
% 4.07/1.02      ( v4_orders_2(X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_15747,c_2425,c_2451,c_2477,c_2503]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15825,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | r3_waybel_9(sK7,X1,sK0(sK7,X0,k1_xboole_0)) = iProver_top
% 4.07/1.02      | m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_15824]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_25,plain,
% 4.07/1.02      ( ~ r3_waybel_9(X0,sK5(X0),X1)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.07/1.02      | v1_compts_1(X0)
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f99]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1735,plain,
% 4.07/1.02      ( ~ r3_waybel_9(X0,sK5(X0),X1)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 4.07/1.02      | v1_compts_1(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_25,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1736,plain,
% 4.07/1.02      ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
% 4.07/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1735]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1740,plain,
% 4.07/1.02      ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
% 4.07/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 4.07/1.02      | v1_compts_1(sK7) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1736,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11778,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,sK5(sK7),X0) != iProver_top
% 4.07/1.02      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1740]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15829,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(sK5(sK7)) = iProver_top
% 4.07/1.02      | v4_orders_2(sK5(sK7)) != iProver_top
% 4.07/1.02      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_15825,c_11778]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_30,plain,
% 4.07/1.02      ( v1_compts_1(X0)
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v2_struct_0(sK5(X0))
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f94]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1665,plain,
% 4.07/1.02      ( v1_compts_1(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v2_struct_0(sK5(X0))
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1666,plain,
% 4.07/1.02      ( v1_compts_1(sK7)
% 4.07/1.02      | ~ v2_struct_0(sK5(sK7))
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1665]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1668,plain,
% 4.07/1.02      ( v1_compts_1(sK7) | ~ v2_struct_0(sK5(sK7)) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1666,c_42,c_41,c_40,c_66]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1670,plain,
% 4.07/1.02      ( v1_compts_1(sK7) = iProver_top | v2_struct_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_29,plain,
% 4.07/1.02      ( v1_compts_1(X0)
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v4_orders_2(sK5(X0))
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f95]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1679,plain,
% 4.07/1.02      ( v1_compts_1(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v4_orders_2(sK5(X0))
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1680,plain,
% 4.07/1.02      ( v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | v4_orders_2(sK5(sK7))
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1679]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1682,plain,
% 4.07/1.02      ( v4_orders_2(sK5(sK7)) | v1_compts_1(sK7) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1680,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1683,plain,
% 4.07/1.02      ( v1_compts_1(sK7) | v4_orders_2(sK5(sK7)) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1682]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1684,plain,
% 4.07/1.02      ( v1_compts_1(sK7) = iProver_top | v4_orders_2(sK5(sK7)) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1683]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_28,plain,
% 4.07/1.02      ( v1_compts_1(X0)
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v7_waybel_0(sK5(X0))
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f96]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1693,plain,
% 4.07/1.02      ( v1_compts_1(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v7_waybel_0(sK5(X0))
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_28,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1694,plain,
% 4.07/1.02      ( v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | v7_waybel_0(sK5(sK7))
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1693]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1696,plain,
% 4.07/1.02      ( v7_waybel_0(sK5(sK7)) | v1_compts_1(sK7) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1694,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1697,plain,
% 4.07/1.02      ( v1_compts_1(sK7) | v7_waybel_0(sK5(sK7)) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1696]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1698,plain,
% 4.07/1.02      ( v1_compts_1(sK7) = iProver_top | v7_waybel_0(sK5(sK7)) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1697]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_27,plain,
% 4.07/1.02      ( l1_waybel_0(sK5(X0),X0)
% 4.07/1.02      | v1_compts_1(X0)
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f97]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1707,plain,
% 4.07/1.02      ( l1_waybel_0(sK5(X0),X0)
% 4.07/1.02      | v1_compts_1(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1708,plain,
% 4.07/1.02      ( l1_waybel_0(sK5(sK7),sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1707]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1710,plain,
% 4.07/1.02      ( l1_waybel_0(sK5(sK7),sK7) | v1_compts_1(sK7) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1708,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1712,plain,
% 4.07/1.02      ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1710]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15862,plain,
% 4.07/1.02      ( v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_15829,c_1670,c_1684,c_1698,c_1712]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15863,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | m1_subset_1(sK0(sK7,X0,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_15862]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15869,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_15624,c_15863]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12085,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,sK5(sK7))
% 4.07/1.02      | l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ l1_waybel_0(sK5(sK7),sK7)
% 4.07/1.02      | v2_struct_0(sK5(sK7))
% 4.07/1.02      | ~ v4_orders_2(sK5(sK7))
% 4.07/1.02      | ~ v7_waybel_0(sK5(sK7)) ),
% 4.07/1.02      inference(instantiation,[status(thm)],[c_2424]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12086,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) = iProver_top
% 4.07/1.02      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(sK5(sK7)) = iProver_top
% 4.07/1.02      | v4_orders_2(sK5(sK7)) != iProver_top
% 4.07/1.02      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_12085]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12084,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,sK5(sK7))
% 4.07/1.02      | ~ l1_waybel_0(sK5(sK7),sK7)
% 4.07/1.02      | v2_struct_0(sK5(sK7))
% 4.07/1.02      | ~ v4_orders_2(sK5(sK7))
% 4.07/1.02      | v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(sK5(sK7)) ),
% 4.07/1.02      inference(instantiation,[status(thm)],[c_2450]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12090,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(sK5(sK7)) = iProver_top
% 4.07/1.02      | v4_orders_2(sK5(sK7)) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) = iProver_top
% 4.07/1.02      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_12084]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12083,plain,
% 4.07/1.02      ( ~ m2_yellow_6(X0,sK7,sK5(sK7))
% 4.07/1.02      | ~ l1_waybel_0(sK5(sK7),sK7)
% 4.07/1.02      | v2_struct_0(sK5(sK7))
% 4.07/1.02      | v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(sK5(sK7))
% 4.07/1.02      | ~ v7_waybel_0(sK5(sK7)) ),
% 4.07/1.02      inference(instantiation,[status(thm)],[c_2476]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12094,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(sK5(sK7)) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(sK5(sK7)) != iProver_top
% 4.07/1.02      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_12083]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15915,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_15869,c_1670,c_1684,c_1698,c_1712,c_12086,c_12090,c_12094,
% 4.07/1.02                 c_15624,c_15863]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15916,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.02      | m2_yellow_6(X0,sK7,sK5(sK7)) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_15915]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15921,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,sK9(sK5(sK7))) = k1_xboole_0
% 4.07/1.02      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(sK9(sK5(sK7))) = iProver_top
% 4.07/1.02      | v2_struct_0(sK5(sK7)) = iProver_top
% 4.07/1.02      | v4_orders_2(sK5(sK7)) != iProver_top
% 4.07/1.02      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_11789,c_15916]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1392,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | ~ v2_struct_0(X3)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | X2 != X0
% 4.07/1.02      | sK9(X2) != X3
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_491,c_39]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1393,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v2_struct_0(sK9(X0))
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1392]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1397,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v2_struct_0(sK9(X0)) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1393,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1398,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v2_struct_0(sK9(X0))
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1397]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1362,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | v4_orders_2(X3)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | X2 != X0
% 4.07/1.02      | sK9(X2) != X3
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_519,c_39]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1363,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1362]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1367,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1363,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1368,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1367]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1332,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | v7_waybel_0(X3)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | X2 != X0
% 4.07/1.02      | sK9(X2) != X3
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_547,c_39]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1333,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | v7_waybel_0(sK9(X0))
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1332]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1337,plain,
% 4.07/1.02      ( v7_waybel_0(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1333,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1338,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | v7_waybel_0(sK9(X0)) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1337]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1302,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | l1_waybel_0(X2,X1)
% 4.07/1.02      | ~ l1_waybel_0(X3,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X3)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(X3)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(X3)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | X3 != X0
% 4.07/1.02      | sK9(X3) != X2
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_575,c_39]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1303,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | l1_waybel_0(sK9(X0),sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1302]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1307,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | l1_waybel_0(sK9(X0),sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1303,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1308,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | l1_waybel_0(sK9(X0),sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1307]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_18,plain,
% 4.07/1.02      ( ~ v3_yellow_6(X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | ~ v2_pre_topc(X1)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 4.07/1.02      inference(cnf_transformation,[],[f84]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_38,negated_conjecture,
% 4.07/1.02      ( v3_yellow_6(sK9(X0),sK7)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f104]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_672,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X2,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | ~ v2_pre_topc(X1)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | v2_struct_0(X2)
% 4.07/1.02      | ~ v4_orders_2(X2)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X2)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(X1)
% 4.07/1.02      | k10_yellow_6(X1,X0) != k1_xboole_0
% 4.07/1.02      | sK9(X2) != X0
% 4.07/1.02      | sK7 != X1 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_673,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ l1_waybel_0(sK9(X0),sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | ~ v2_pre_topc(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK9(X0))
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(sK9(X0))
% 4.07/1.02      | ~ l1_pre_topc(sK7)
% 4.07/1.02      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_672]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_677,plain,
% 4.07/1.02      ( ~ v7_waybel_0(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | ~ l1_waybel_0(sK9(X0),sK7)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK9(X0))
% 4.07/1.02      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_673,c_42,c_41,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_678,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ l1_waybel_0(sK9(X0),sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK9(X0))
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(sK9(X0))
% 4.07/1.02      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_677]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1578,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK9(X0))
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v7_waybel_0(sK9(X0))
% 4.07/1.02      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 4.07/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_1308,c_678]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1592,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK9(X0))
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v4_orders_2(sK9(X0))
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 4.07/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_1338,c_1578]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1601,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK9(X0))
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 4.07/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_1368,c_1592]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1610,plain,
% 4.07/1.02      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 4.07/1.02      inference(backward_subsumption_resolution,[status(thm)],[c_1398,c_1601]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12243,plain,
% 4.07/1.02      ( ~ l1_waybel_0(sK5(sK7),sK7)
% 4.07/1.02      | v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(sK5(sK7))
% 4.07/1.02      | ~ v4_orders_2(sK5(sK7))
% 4.07/1.02      | ~ v7_waybel_0(sK5(sK7))
% 4.07/1.02      | k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0 ),
% 4.07/1.02      inference(instantiation,[status(thm)],[c_1610]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12244,plain,
% 4.07/1.02      ( k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0
% 4.07/1.02      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(sK5(sK7)) = iProver_top
% 4.07/1.02      | v4_orders_2(sK5(sK7)) != iProver_top
% 4.07/1.02      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_12243]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11780,plain,
% 4.07/1.02      ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1710]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11759,plain,
% 4.07/1.02      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 4.07/1.02      | l1_waybel_0(X1,sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) != iProver_top
% 4.07/1.02      | v2_struct_0(X1) = iProver_top
% 4.07/1.02      | v4_orders_2(X1) != iProver_top
% 4.07/1.02      | v7_waybel_0(X1) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12020,plain,
% 4.07/1.02      ( l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v2_struct_0(sK9(X0)) != iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_11789,c_11759]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_12238,plain,
% 4.07/1.02      ( v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(sK9(sK5(sK7))) != iProver_top
% 4.07/1.02      | v2_struct_0(sK5(sK7)) = iProver_top
% 4.07/1.02      | v4_orders_2(sK5(sK7)) != iProver_top
% 4.07/1.02      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 4.07/1.02      inference(superposition,[status(thm)],[c_11780,c_12020]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_13274,plain,
% 4.07/1.02      ( v2_struct_0(sK9(sK5(sK7))) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) = iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_12238,c_1670,c_1684,c_1698]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_13275,plain,
% 4.07/1.02      ( v1_compts_1(sK7) = iProver_top
% 4.07/1.02      | v2_struct_0(sK9(sK5(sK7))) != iProver_top ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_13274]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_15961,plain,
% 4.07/1.02      ( v1_compts_1(sK7) = iProver_top ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_15921,c_1670,c_1684,c_1698,c_1712,c_12244,c_13275]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_23,plain,
% 4.07/1.02      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | ~ v1_compts_1(X0)
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f91]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1756,plain,
% 4.07/1.02      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | ~ v1_compts_1(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1757,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1756]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1761,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1757,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1762,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ v1_compts_1(sK7)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1761]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11777,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,sK4(sK7,X0)) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | v1_compts_1(sK7) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.02      | v4_orders_2(X0) != iProver_top
% 4.07/1.02      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.02      inference(predicate_to_equality,[status(thm)],[c_1762]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_22,plain,
% 4.07/1.02      ( ~ r3_waybel_9(X0,X1,X2)
% 4.07/1.02      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | ~ v2_pre_topc(X0)
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0) ),
% 4.07/1.02      inference(cnf_transformation,[],[f88]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1786,plain,
% 4.07/1.02      ( ~ r3_waybel_9(X0,X1,X2)
% 4.07/1.02      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 4.07/1.02      | ~ l1_waybel_0(X1,X0)
% 4.07/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(X1)
% 4.07/1.02      | ~ v4_orders_2(X1)
% 4.07/1.02      | ~ v7_waybel_0(X1)
% 4.07/1.02      | ~ l1_pre_topc(X0)
% 4.07/1.02      | sK7 != X0 ),
% 4.07/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_41]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1787,plain,
% 4.07/1.02      ( ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | v2_struct_0(sK7)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ l1_pre_topc(sK7) ),
% 4.07/1.02      inference(unflattening,[status(thm)],[c_1786]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1791,plain,
% 4.07/1.02      ( ~ v7_waybel_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0) ),
% 4.07/1.02      inference(global_propositional_subsumption,
% 4.07/1.02                [status(thm)],
% 4.07/1.02                [c_1787,c_42,c_40]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_1792,plain,
% 4.07/1.02      ( ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.02      | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
% 4.07/1.02      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.02      | v2_struct_0(X0)
% 4.07/1.02      | ~ v4_orders_2(X0)
% 4.07/1.02      | ~ v7_waybel_0(X0) ),
% 4.07/1.02      inference(renaming,[status(thm)],[c_1791]) ).
% 4.07/1.02  
% 4.07/1.02  cnf(c_11776,plain,
% 4.07/1.02      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 4.07/1.02      | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0) = iProver_top
% 4.07/1.02      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.02      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.02      | v2_struct_0(X0) = iProver_top
% 4.07/1.03      | v4_orders_2(X0) != iProver_top
% 4.07/1.03      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_17,plain,
% 4.07/1.03      ( v3_yellow_6(X0,X1)
% 4.07/1.03      | ~ l1_waybel_0(X0,X1)
% 4.07/1.03      | ~ v2_pre_topc(X1)
% 4.07/1.03      | v2_struct_0(X1)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ l1_pre_topc(X1)
% 4.07/1.03      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 4.07/1.03      inference(cnf_transformation,[],[f85]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_33,negated_conjecture,
% 4.07/1.03      ( ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | ~ v3_yellow_6(X0,sK7)
% 4.07/1.03      | ~ v1_compts_1(sK7) ),
% 4.07/1.03      inference(cnf_transformation,[],[f109]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_639,plain,
% 4.07/1.03      ( ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | ~ l1_waybel_0(X1,X2)
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | ~ v2_pre_topc(X2)
% 4.07/1.03      | v2_struct_0(X1)
% 4.07/1.03      | v2_struct_0(X2)
% 4.07/1.03      | ~ v4_orders_2(X1)
% 4.07/1.03      | ~ v7_waybel_0(X1)
% 4.07/1.03      | ~ l1_pre_topc(X2)
% 4.07/1.03      | X0 != X1
% 4.07/1.03      | k10_yellow_6(X2,X1) = k1_xboole_0
% 4.07/1.03      | sK7 != X2 ),
% 4.07/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_640,plain,
% 4.07/1.03      ( ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | ~ v2_pre_topc(sK7)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | v2_struct_0(sK7)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ l1_pre_topc(sK7)
% 4.07/1.03      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 4.07/1.03      inference(unflattening,[status(thm)],[c_639]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_644,plain,
% 4.07/1.03      ( ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_640,c_42,c_41,c_40]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_645,plain,
% 4.07/1.03      ( ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0)
% 4.07/1.03      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 4.07/1.03      inference(renaming,[status(thm)],[c_644]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11786,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.03      | m2_yellow_6(X0,sK7,sK8) != iProver_top
% 4.07/1.03      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(X0) = iProver_top
% 4.07/1.03      | v4_orders_2(X0) != iProver_top
% 4.07/1.03      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_37,negated_conjecture,
% 4.07/1.03      ( ~ v1_compts_1(sK7) | ~ v2_struct_0(sK8) ),
% 4.07/1.03      inference(cnf_transformation,[],[f105]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_52,plain,
% 4.07/1.03      ( v1_compts_1(sK7) != iProver_top | v2_struct_0(sK8) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_36,negated_conjecture,
% 4.07/1.03      ( ~ v1_compts_1(sK7) | v4_orders_2(sK8) ),
% 4.07/1.03      inference(cnf_transformation,[],[f106]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_53,plain,
% 4.07/1.03      ( v1_compts_1(sK7) != iProver_top | v4_orders_2(sK8) = iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_35,negated_conjecture,
% 4.07/1.03      ( ~ v1_compts_1(sK7) | v7_waybel_0(sK8) ),
% 4.07/1.03      inference(cnf_transformation,[],[f107]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_54,plain,
% 4.07/1.03      ( v1_compts_1(sK7) != iProver_top | v7_waybel_0(sK8) = iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_34,negated_conjecture,
% 4.07/1.03      ( l1_waybel_0(sK8,sK7) | ~ v1_compts_1(sK7) ),
% 4.07/1.03      inference(cnf_transformation,[],[f108]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_55,plain,
% 4.07/1.03      ( l1_waybel_0(sK8,sK7) = iProver_top | v1_compts_1(sK7) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_646,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.03      | m2_yellow_6(X0,sK7,sK8) != iProver_top
% 4.07/1.03      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(X0) = iProver_top
% 4.07/1.03      | v4_orders_2(X0) != iProver_top
% 4.07/1.03      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11895,plain,
% 4.07/1.03      ( ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | l1_waybel_0(X0,sK7)
% 4.07/1.03      | ~ l1_waybel_0(sK8,sK7)
% 4.07/1.03      | v2_struct_0(sK8)
% 4.07/1.03      | ~ v4_orders_2(sK8)
% 4.07/1.03      | ~ v7_waybel_0(sK8) ),
% 4.07/1.03      inference(instantiation,[status(thm)],[c_2424]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11896,plain,
% 4.07/1.03      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 4.07/1.03      | l1_waybel_0(X0,sK7) = iProver_top
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_11895]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11900,plain,
% 4.07/1.03      ( ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | ~ l1_waybel_0(sK8,sK7)
% 4.07/1.03      | v2_struct_0(sK8)
% 4.07/1.03      | ~ v4_orders_2(sK8)
% 4.07/1.03      | v7_waybel_0(X0)
% 4.07/1.03      | ~ v7_waybel_0(sK8) ),
% 4.07/1.03      inference(instantiation,[status(thm)],[c_2450]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11901,plain,
% 4.07/1.03      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(X0) = iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_11900]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11907,plain,
% 4.07/1.03      ( ~ m2_yellow_6(X0,sK7,sK8)
% 4.07/1.03      | ~ l1_waybel_0(sK8,sK7)
% 4.07/1.03      | v2_struct_0(sK8)
% 4.07/1.03      | v4_orders_2(X0)
% 4.07/1.03      | ~ v4_orders_2(sK8)
% 4.07/1.03      | ~ v7_waybel_0(sK8) ),
% 4.07/1.03      inference(instantiation,[status(thm)],[c_2476]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11908,plain,
% 4.07/1.03      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(X0) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_11907]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_12841,plain,
% 4.07/1.03      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 4.07/1.03      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(X0) = iProver_top ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_11786,c_52,c_53,c_54,c_55,c_646,c_11896,c_11901,c_11908]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_12842,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 4.07/1.03      | m2_yellow_6(X0,sK7,sK8) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(X0) = iProver_top ),
% 4.07/1.03      inference(renaming,[status(thm)],[c_12841]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_13307,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
% 4.07/1.03      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK3(sK7,sK8,X0)) = iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(superposition,[status(thm)],[c_11776,c_12842]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_13774,plain,
% 4.07/1.03      ( v2_struct_0(sK3(sK7,sK8,X0)) = iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
% 4.07/1.03      | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_13307,c_52,c_53,c_54,c_55]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_13775,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
% 4.07/1.03      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 4.07/1.03      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK3(sK7,sK8,X0)) = iProver_top ),
% 4.07/1.03      inference(renaming,[status(thm)],[c_13774]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_13311,plain,
% 4.07/1.03      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 4.07/1.03      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.03      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v2_struct_0(X0) = iProver_top
% 4.07/1.03      | v2_struct_0(sK3(sK7,X0,X1)) != iProver_top
% 4.07/1.03      | v4_orders_2(X0) != iProver_top
% 4.07/1.03      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.03      inference(superposition,[status(thm)],[c_11776,c_11759]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_13780,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
% 4.07/1.03      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(superposition,[status(thm)],[c_13775,c_13311]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_14395,plain,
% 4.07/1.03      ( v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
% 4.07/1.03      | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_13780,c_52,c_53,c_54,c_55]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_14396,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,sK3(sK7,sK8,X0)) = k1_xboole_0
% 4.07/1.03      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 4.07/1.03      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top ),
% 4.07/1.03      inference(renaming,[status(thm)],[c_14395]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_14402,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(superposition,[status(thm)],[c_11777,c_14396]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_24,plain,
% 4.07/1.03      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.03      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 4.07/1.03      | ~ v1_compts_1(X1)
% 4.07/1.03      | ~ v2_pre_topc(X1)
% 4.07/1.03      | v2_struct_0(X1)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ l1_pre_topc(X1) ),
% 4.07/1.03      inference(cnf_transformation,[],[f90]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_2094,plain,
% 4.07/1.03      ( ~ l1_waybel_0(X0,X1)
% 4.07/1.03      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 4.07/1.03      | ~ v1_compts_1(X1)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | v2_struct_0(X1)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ l1_pre_topc(X1)
% 4.07/1.03      | sK7 != X1 ),
% 4.07/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_41]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_2095,plain,
% 4.07/1.03      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | v2_struct_0(sK7)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ l1_pre_topc(sK7) ),
% 4.07/1.03      inference(unflattening,[status(thm)],[c_2094]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_2099,plain,
% 4.07/1.03      ( ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | v2_struct_0(X0) ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_2095,c_42,c_40]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_2100,plain,
% 4.07/1.03      ( ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0) ),
% 4.07/1.03      inference(renaming,[status(thm)],[c_2099]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11875,plain,
% 4.07/1.03      ( ~ l1_waybel_0(sK8,sK7)
% 4.07/1.03      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | v2_struct_0(sK8)
% 4.07/1.03      | ~ v4_orders_2(sK8)
% 4.07/1.03      | ~ v7_waybel_0(sK8) ),
% 4.07/1.03      inference(instantiation,[status(thm)],[c_2100]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11876,plain,
% 4.07/1.03      ( l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_11875]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_14523,plain,
% 4.07/1.03      ( v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_14402,c_52,c_53,c_54,c_55,c_11876]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_14524,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top ),
% 4.07/1.03      inference(renaming,[status(thm)],[c_14523]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_15966,plain,
% 4.07/1.03      ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
% 4.07/1.03      inference(superposition,[status(thm)],[c_15961,c_14524]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_21,plain,
% 4.07/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 4.07/1.03      | ~ l1_waybel_0(X1,X0)
% 4.07/1.03      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 4.07/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.03      | ~ v2_pre_topc(X0)
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | v2_struct_0(X1)
% 4.07/1.03      | ~ v4_orders_2(X1)
% 4.07/1.03      | ~ v7_waybel_0(X1)
% 4.07/1.03      | ~ l1_pre_topc(X0) ),
% 4.07/1.03      inference(cnf_transformation,[],[f89]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_1819,plain,
% 4.07/1.03      ( ~ r3_waybel_9(X0,X1,X2)
% 4.07/1.03      | ~ l1_waybel_0(X1,X0)
% 4.07/1.03      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 4.07/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | v2_struct_0(X1)
% 4.07/1.03      | ~ v4_orders_2(X1)
% 4.07/1.03      | ~ v7_waybel_0(X1)
% 4.07/1.03      | ~ l1_pre_topc(X0)
% 4.07/1.03      | sK7 != X0 ),
% 4.07/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_41]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_1820,plain,
% 4.07/1.03      ( ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.03      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
% 4.07/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | v2_struct_0(sK7)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ l1_pre_topc(sK7) ),
% 4.07/1.03      inference(unflattening,[status(thm)],[c_1819]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_1824,plain,
% 4.07/1.03      ( ~ v7_waybel_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.03      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
% 4.07/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.03      | v2_struct_0(X0) ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_1820,c_42,c_40]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_1825,plain,
% 4.07/1.03      ( ~ r3_waybel_9(sK7,X0,X1)
% 4.07/1.03      | ~ l1_waybel_0(X0,sK7)
% 4.07/1.03      | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
% 4.07/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 4.07/1.03      | v2_struct_0(X0)
% 4.07/1.03      | ~ v4_orders_2(X0)
% 4.07/1.03      | ~ v7_waybel_0(X0) ),
% 4.07/1.03      inference(renaming,[status(thm)],[c_1824]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11775,plain,
% 4.07/1.03      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 4.07/1.03      | l1_waybel_0(X0,sK7) != iProver_top
% 4.07/1.03      | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1))) = iProver_top
% 4.07/1.03      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v2_struct_0(X0) = iProver_top
% 4.07/1.03      | v4_orders_2(X0) != iProver_top
% 4.07/1.03      | v7_waybel_0(X0) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_1825]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_16083,plain,
% 4.07/1.03      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) != iProver_top
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top
% 4.07/1.03      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(superposition,[status(thm)],[c_15966,c_11775]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11886,plain,
% 4.07/1.03      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 4.07/1.03      | ~ l1_waybel_0(sK8,sK7)
% 4.07/1.03      | ~ v1_compts_1(sK7)
% 4.07/1.03      | v2_struct_0(sK8)
% 4.07/1.03      | ~ v4_orders_2(sK8)
% 4.07/1.03      | ~ v7_waybel_0(sK8) ),
% 4.07/1.03      inference(instantiation,[status(thm)],[c_1762]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_11887,plain,
% 4.07/1.03      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 4.07/1.03      | l1_waybel_0(sK8,sK7) != iProver_top
% 4.07/1.03      | v1_compts_1(sK7) != iProver_top
% 4.07/1.03      | v2_struct_0(sK8) = iProver_top
% 4.07/1.03      | v4_orders_2(sK8) != iProver_top
% 4.07/1.03      | v7_waybel_0(sK8) != iProver_top ),
% 4.07/1.03      inference(predicate_to_equality,[status(thm)],[c_11886]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_16152,plain,
% 4.07/1.03      ( r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top ),
% 4.07/1.03      inference(global_propositional_subsumption,
% 4.07/1.03                [status(thm)],
% 4.07/1.03                [c_16083,c_52,c_53,c_54,c_55,c_1670,c_1684,c_1698,c_1712,
% 4.07/1.03                 c_11876,c_11887,c_12244,c_13275,c_15921]) ).
% 4.07/1.03  
% 4.07/1.03  cnf(c_16156,plain,
% 4.07/1.03      ( $false ),
% 4.07/1.03      inference(superposition,[status(thm)],[c_16152,c_12529]) ).
% 4.07/1.03  
% 4.07/1.03  
% 4.07/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/1.03  
% 4.07/1.03  ------                               Statistics
% 4.07/1.03  
% 4.07/1.03  ------ General
% 4.07/1.03  
% 4.07/1.03  abstr_ref_over_cycles:                  0
% 4.07/1.03  abstr_ref_under_cycles:                 0
% 4.07/1.03  gc_basic_clause_elim:                   0
% 4.07/1.03  forced_gc_time:                         0
% 4.07/1.03  parsing_time:                           0.013
% 4.07/1.03  unif_index_cands_time:                  0.
% 4.07/1.03  unif_index_add_time:                    0.
% 4.07/1.03  orderings_time:                         0.
% 4.07/1.03  out_proof_time:                         0.024
% 4.07/1.03  total_time:                             0.475
% 4.07/1.03  num_of_symbols:                         62
% 4.07/1.03  num_of_terms:                           7998
% 4.07/1.03  
% 4.07/1.03  ------ Preprocessing
% 4.07/1.03  
% 4.07/1.03  num_of_splits:                          0
% 4.07/1.03  num_of_split_atoms:                     0
% 4.07/1.03  num_of_reused_defs:                     0
% 4.07/1.03  num_eq_ax_congr_red:                    52
% 4.07/1.03  num_of_sem_filtered_clauses:            1
% 4.07/1.03  num_of_subtypes:                        0
% 4.07/1.03  monotx_restored_types:                  0
% 4.07/1.03  sat_num_of_epr_types:                   0
% 4.07/1.03  sat_num_of_non_cyclic_types:            0
% 4.07/1.03  sat_guarded_non_collapsed_types:        0
% 4.07/1.03  num_pure_diseq_elim:                    0
% 4.07/1.03  simp_replaced_by:                       0
% 4.07/1.03  res_preprocessed:                       203
% 4.07/1.03  prep_upred:                             0
% 4.07/1.03  prep_unflattend:                        285
% 4.07/1.03  smt_new_axioms:                         0
% 4.07/1.03  pred_elim_cands:                        11
% 4.07/1.03  pred_elim:                              5
% 4.07/1.03  pred_elim_cl:                           6
% 4.07/1.03  pred_elim_cycles:                       18
% 4.07/1.03  merged_defs:                            0
% 4.07/1.03  merged_defs_ncl:                        0
% 4.07/1.03  bin_hyper_res:                          0
% 4.07/1.03  prep_cycles:                            4
% 4.07/1.03  pred_elim_time:                         0.185
% 4.07/1.03  splitting_time:                         0.
% 4.07/1.03  sem_filter_time:                        0.
% 4.07/1.03  monotx_time:                            0.
% 4.07/1.03  subtype_inf_time:                       0.
% 4.07/1.03  
% 4.07/1.03  ------ Problem properties
% 4.07/1.03  
% 4.07/1.03  clauses:                                37
% 4.07/1.03  conjectures:                            6
% 4.07/1.03  epr:                                    9
% 4.07/1.03  horn:                                   11
% 4.07/1.03  ground:                                 10
% 4.07/1.03  unary:                                  2
% 4.07/1.03  binary:                                 10
% 4.07/1.03  lits:                                   185
% 4.07/1.03  lits_eq:                                6
% 4.07/1.03  fd_pure:                                0
% 4.07/1.03  fd_pseudo:                              0
% 4.07/1.03  fd_cond:                                0
% 4.07/1.03  fd_pseudo_cond:                         4
% 4.07/1.03  ac_symbols:                             0
% 4.07/1.03  
% 4.07/1.03  ------ Propositional Solver
% 4.07/1.03  
% 4.07/1.03  prop_solver_calls:                      28
% 4.07/1.03  prop_fast_solver_calls:                 5874
% 4.07/1.03  smt_solver_calls:                       0
% 4.07/1.03  smt_fast_solver_calls:                  0
% 4.07/1.03  prop_num_of_clauses:                    3383
% 4.07/1.03  prop_preprocess_simplified:             11134
% 4.07/1.03  prop_fo_subsumed:                       209
% 4.07/1.03  prop_solver_time:                       0.
% 4.07/1.03  smt_solver_time:                        0.
% 4.07/1.03  smt_fast_solver_time:                   0.
% 4.07/1.03  prop_fast_solver_time:                  0.
% 4.07/1.03  prop_unsat_core_time:                   0.
% 4.07/1.03  
% 4.07/1.03  ------ QBF
% 4.07/1.03  
% 4.07/1.03  qbf_q_res:                              0
% 4.07/1.03  qbf_num_tautologies:                    0
% 4.07/1.03  qbf_prep_cycles:                        0
% 4.07/1.03  
% 4.07/1.03  ------ BMC1
% 4.07/1.03  
% 4.07/1.03  bmc1_current_bound:                     -1
% 4.07/1.03  bmc1_last_solved_bound:                 -1
% 4.07/1.03  bmc1_unsat_core_size:                   -1
% 4.07/1.03  bmc1_unsat_core_parents_size:           -1
% 4.07/1.03  bmc1_merge_next_fun:                    0
% 4.07/1.03  bmc1_unsat_core_clauses_time:           0.
% 4.07/1.03  
% 4.07/1.03  ------ Instantiation
% 4.07/1.03  
% 4.07/1.03  inst_num_of_clauses:                    784
% 4.07/1.03  inst_num_in_passive:                    95
% 4.07/1.03  inst_num_in_active:                     523
% 4.07/1.03  inst_num_in_unprocessed:                166
% 4.07/1.03  inst_num_of_loops:                      580
% 4.07/1.03  inst_num_of_learning_restarts:          0
% 4.07/1.03  inst_num_moves_active_passive:          53
% 4.07/1.03  inst_lit_activity:                      0
% 4.07/1.03  inst_lit_activity_moves:                0
% 4.07/1.03  inst_num_tautologies:                   0
% 4.07/1.03  inst_num_prop_implied:                  0
% 4.07/1.03  inst_num_existing_simplified:           0
% 4.07/1.03  inst_num_eq_res_simplified:             0
% 4.07/1.03  inst_num_child_elim:                    0
% 4.07/1.03  inst_num_of_dismatching_blockings:      150
% 4.07/1.03  inst_num_of_non_proper_insts:           768
% 4.07/1.03  inst_num_of_duplicates:                 0
% 4.07/1.03  inst_inst_num_from_inst_to_res:         0
% 4.07/1.03  inst_dismatching_checking_time:         0.
% 4.07/1.03  
% 4.07/1.03  ------ Resolution
% 4.07/1.03  
% 4.07/1.03  res_num_of_clauses:                     0
% 4.07/1.03  res_num_in_passive:                     0
% 4.07/1.03  res_num_in_active:                      0
% 4.07/1.03  res_num_of_loops:                       207
% 4.07/1.03  res_forward_subset_subsumed:            16
% 4.07/1.03  res_backward_subset_subsumed:           0
% 4.07/1.03  res_forward_subsumed:                   0
% 4.07/1.03  res_backward_subsumed:                  0
% 4.07/1.03  res_forward_subsumption_resolution:     21
% 4.07/1.03  res_backward_subsumption_resolution:    6
% 4.07/1.03  res_clause_to_clause_subsumption:       1476
% 4.07/1.03  res_orphan_elimination:                 0
% 4.07/1.03  res_tautology_del:                      47
% 4.07/1.03  res_num_eq_res_simplified:              0
% 4.07/1.03  res_num_sel_changes:                    0
% 4.07/1.03  res_moves_from_active_to_pass:          0
% 4.07/1.03  
% 4.07/1.03  ------ Superposition
% 4.07/1.03  
% 4.07/1.03  sup_time_total:                         0.
% 4.07/1.03  sup_time_generating:                    0.
% 4.07/1.03  sup_time_sim_full:                      0.
% 4.07/1.03  sup_time_sim_immed:                     0.
% 4.07/1.03  
% 4.07/1.03  sup_num_of_clauses:                     120
% 4.07/1.03  sup_num_in_active:                      70
% 4.07/1.03  sup_num_in_passive:                     50
% 4.07/1.03  sup_num_of_loops:                       114
% 4.07/1.03  sup_fw_superposition:                   54
% 4.07/1.03  sup_bw_superposition:                   152
% 4.07/1.03  sup_immediate_simplified:               71
% 4.07/1.03  sup_given_eliminated:                   1
% 4.07/1.03  comparisons_done:                       0
% 4.07/1.03  comparisons_avoided:                    0
% 4.07/1.03  
% 4.07/1.03  ------ Simplifications
% 4.07/1.03  
% 4.07/1.03  
% 4.07/1.03  sim_fw_subset_subsumed:                 20
% 4.07/1.03  sim_bw_subset_subsumed:                 18
% 4.07/1.03  sim_fw_subsumed:                        44
% 4.07/1.03  sim_bw_subsumed:                        29
% 4.07/1.03  sim_fw_subsumption_res:                 0
% 4.07/1.03  sim_bw_subsumption_res:                 0
% 4.07/1.03  sim_tautology_del:                      13
% 4.07/1.03  sim_eq_tautology_del:                   7
% 4.07/1.03  sim_eq_res_simp:                        0
% 4.07/1.03  sim_fw_demodulated:                     3
% 4.07/1.03  sim_bw_demodulated:                     1
% 4.07/1.03  sim_light_normalised:                   19
% 4.07/1.03  sim_joinable_taut:                      0
% 4.07/1.03  sim_joinable_simp:                      0
% 4.07/1.03  sim_ac_normalised:                      0
% 4.07/1.03  sim_smt_subsumption:                    0
% 4.07/1.03  
%------------------------------------------------------------------------------
