%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:26 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

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
    inference(rectify,[],[f59])).

fof(f63,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK9(X3),X0)
        & m2_yellow_6(sK9(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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

fof(f61,plain,
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

fof(f64,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f60,f63,f62,f61])).

fof(f101,plain,(
    ! [X3] :
      ( m2_yellow_6(sK9(X3),sK7,X3)
      | ~ l1_waybel_0(X3,sK7)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f64])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f98,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f100,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f64])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(rectify,[],[f42])).

fof(f46,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f56,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK6(X0,X3))
        & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f54,f56,f55])).

fof(f97,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK5(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK5(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK5(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X3] :
      ( v3_yellow_6(sK9(X3),sK7)
      | ~ l1_waybel_0(X3,sK7)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f64])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f51])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
        & m2_yellow_6(sK3(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f49])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK7)
      | ~ m2_yellow_6(X2,sK7,sK8)
      | ~ v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f103,plain,
    ( ~ v2_struct_0(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f104,plain,
    ( v4_orders_2(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f105,plain,
    ( v7_waybel_0(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f106,plain,
    ( l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f50])).

cnf(c_39,negated_conjecture,
    ( m2_yellow_6(sK9(X0),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_11061,negated_conjecture,
    ( m2_yellow_6(sK9(X0_59),sK7,X0_59)
    | ~ l1_waybel_0(X0_59,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_11824,plain,
    ( m2_yellow_6(sK9(X0_59),sK7,X0_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11061])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_41,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2120,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_41])).

cnf(c_2121,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_2120])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2125,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2121,c_42,c_40])).

cnf(c_2126,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_2125])).

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
    inference(cnf_transformation,[],[f109])).

cnf(c_1913,plain,
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

cnf(c_1914,plain,
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
    inference(unflattening,[status(thm)],[c_1913])).

cnf(c_1918,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1914,c_42,c_40])).

cnf(c_1919,plain,
    ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1918])).

cnf(c_2143,plain,
    ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2126,c_1919])).

cnf(c_11039,plain,
    ( m1_connsp_2(sK2(sK7,X0_59,X1_59),sK7,X1_59)
    | ~ l1_waybel_0(X0_59,sK7)
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_2143])).

cnf(c_11846,plain,
    ( m1_connsp_2(sK2(sK7,X0_59,X1_59),sK7,X1_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) = iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11039])).

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
    inference(cnf_transformation,[],[f74])).

cnf(c_2228,plain,
    ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
    | r1_waybel_0(X1,X2,X0)
    | ~ l1_waybel_0(X2,X1)
    | r2_hidden(sK0(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X2) = X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_41])).

cnf(c_2229,plain,
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
    inference(unflattening,[status(thm)],[c_2228])).

cnf(c_2233,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | r2_hidden(sK0(sK7,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X1)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2229,c_42,c_40])).

cnf(c_2234,plain,
    ( ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | r2_hidden(sK0(sK7,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(renaming,[status(thm)],[c_2233])).

cnf(c_11035,plain,
    ( ~ m1_connsp_2(X0_60,sK7,sK0(sK7,X0_59,X1_59))
    | r1_waybel_0(sK7,X0_59,X0_60)
    | ~ l1_waybel_0(X0_59,sK7)
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59)
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | k10_yellow_6(sK7,X0_59) = X1_59 ),
    inference(subtyping,[status(esa)],[c_2234])).

cnf(c_11850,plain,
    ( k10_yellow_6(sK7,X0_59) = X1_59
    | m1_connsp_2(X0_60,sK7,sK0(sK7,X0_59,X1_59)) != iProver_top
    | r1_waybel_0(sK7,X0_59,X0_60) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11035])).

cnf(c_14127,plain,
    ( k10_yellow_6(sK7,X0_59) = X1_59
    | r1_waybel_0(sK7,X0_59,sK2(sK7,X2_59,sK0(sK7,X0_59,X1_59))) = iProver_top
    | l1_waybel_0(X2_59,sK7) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X2_59)) = iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X2_59) != iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X2_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_11846,c_11850])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_2195,plain,
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

cnf(c_2196,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_2195])).

cnf(c_2200,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2196,c_42,c_40])).

cnf(c_2201,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(renaming,[status(thm)],[c_2200])).

cnf(c_11036,plain,
    ( ~ l1_waybel_0(X0_59,sK7)
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | k10_yellow_6(sK7,X0_59) = X1_59 ),
    inference(subtyping,[status(esa)],[c_2201])).

cnf(c_11166,plain,
    ( k10_yellow_6(sK7,X0_59) = X1_59
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11036])).

cnf(c_15380,plain,
    ( m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X2_59)) = iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | l1_waybel_0(X2_59,sK7) != iProver_top
    | r1_waybel_0(sK7,X0_59,sK2(sK7,X2_59,sK0(sK7,X0_59,X1_59))) = iProver_top
    | k10_yellow_6(sK7,X0_59) = X1_59
    | v2_struct_0(X2_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X2_59) != iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X2_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14127,c_11166])).

cnf(c_15381,plain,
    ( k10_yellow_6(sK7,X0_59) = X1_59
    | r1_waybel_0(sK7,X0_59,sK2(sK7,X2_59,sK0(sK7,X0_59,X1_59))) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | l1_waybel_0(X2_59,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X2_59)) = iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v4_orders_2(X2_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top
    | v7_waybel_0(X2_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_15380])).

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
    inference(cnf_transformation,[],[f108])).

cnf(c_1949,plain,
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

cnf(c_1950,plain,
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
    inference(unflattening,[status(thm)],[c_1949])).

cnf(c_1954,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1950,c_42,c_40])).

cnf(c_1955,plain,
    ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1954])).

cnf(c_2144,plain,
    ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2126,c_1955])).

cnf(c_11038,plain,
    ( ~ r1_waybel_0(sK7,X0_59,sK2(sK7,X0_59,X1_59))
    | ~ l1_waybel_0(X0_59,sK7)
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_2144])).

cnf(c_11847,plain,
    ( r1_waybel_0(sK7,X0_59,sK2(sK7,X0_59,X1_59)) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) = iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11038])).

cnf(c_15403,plain,
    ( k10_yellow_6(sK7,X0_59) = X1_59
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X0_59)) = iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_15381,c_11847])).

cnf(c_20983,plain,
    ( m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X0_59)) = iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | k10_yellow_6(sK7,X0_59) = X1_59
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15403,c_11166])).

cnf(c_20984,plain,
    ( k10_yellow_6(sK7,X0_59) = X1_59
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
    | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X0_59)) = iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_20983])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_475,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_11059,plain,
    ( ~ r2_hidden(X0_59,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_476])).

cnf(c_11826,plain,
    ( r2_hidden(X0_59,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11059])).

cnf(c_21004,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,k1_xboole_0),k10_yellow_6(sK7,X0_59)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_20984,c_11826])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11067,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_61)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_12509,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(instantiation,[status(thm)],[c_11067])).

cnf(c_12512,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12509])).

cnf(c_21142,plain,
    ( r2_hidden(sK0(sK7,X0_59,k1_xboole_0),k10_yellow_6(sK7,X0_59)) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21004,c_12512])).

cnf(c_21143,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(sK0(sK7,X0_59,k1_xboole_0),k10_yellow_6(sK7,X0_59)) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_21142])).

cnf(c_11040,plain,
    ( ~ l1_waybel_0(X0_59,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0_59),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_2126])).

cnf(c_11845,plain,
    ( l1_waybel_0(X0_59,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0_59),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11040])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11066,plain,
    ( ~ r2_hidden(X0_59,X1_59)
    | m1_subset_1(X0_59,X0_61)
    | ~ m1_subset_1(X1_59,k1_zfmisc_1(X0_61)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_11819,plain,
    ( r2_hidden(X0_59,X1_59) != iProver_top
    | m1_subset_1(X0_59,X0_61) = iProver_top
    | m1_subset_1(X1_59,k1_zfmisc_1(X0_61)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11066])).

cnf(c_12656,plain,
    ( l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_11845,c_11819])).

cnf(c_21156,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_21143,c_12656])).

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
    inference(cnf_transformation,[],[f84])).

cnf(c_1880,plain,
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

cnf(c_1881,plain,
    ( r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1880])).

cnf(c_1885,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1881,c_42,c_40])).

cnf(c_1886,plain,
    ( r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1885])).

cnf(c_11045,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59)
    | ~ l1_waybel_0(X0_59,sK7)
    | ~ r2_hidden(X1_59,k10_yellow_6(sK7,X0_59))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1886])).

cnf(c_11840,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11045])).

cnf(c_11151,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11045])).

cnf(c_13731,plain,
    ( r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11840,c_11151,c_12656])).

cnf(c_13732,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_13731])).

cnf(c_21155,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | r3_waybel_9(sK7,X0_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_21143,c_13732])).

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
    inference(cnf_transformation,[],[f85])).

cnf(c_1848,plain,
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

cnf(c_1849,plain,
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
    inference(unflattening,[status(thm)],[c_1848])).

cnf(c_1851,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,X2,X1)
    | ~ m2_yellow_6(X0,sK7,X2)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1849,c_42,c_40])).

cnf(c_1852,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,X2,X1)
    | ~ m2_yellow_6(X0,sK7,X2)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1851])).

cnf(c_11046,plain,
    ( ~ r3_waybel_9(sK7,X0_59,X1_59)
    | r3_waybel_9(sK7,X2_59,X1_59)
    | ~ m2_yellow_6(X0_59,sK7,X2_59)
    | ~ l1_waybel_0(X2_59,sK7)
    | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
    | v2_struct_0(X2_59)
    | ~ v4_orders_2(X2_59)
    | ~ v7_waybel_0(X2_59) ),
    inference(subtyping,[status(esa)],[c_1852])).

cnf(c_11839,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
    | r3_waybel_9(sK7,X2_59,X1_59) = iProver_top
    | m2_yellow_6(X0_59,sK7,X2_59) != iProver_top
    | l1_waybel_0(X2_59,sK7) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X2_59) = iProver_top
    | v4_orders_2(X2_59) != iProver_top
    | v7_waybel_0(X2_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11046])).

cnf(c_21399,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | r3_waybel_9(sK7,X1_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v4_orders_2(X1_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top
    | v7_waybel_0(X1_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_21155,c_11839])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_570,plain,
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

cnf(c_571,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_2416,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_40])).

cnf(c_2417,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | l1_waybel_0(X0,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2416])).

cnf(c_2419,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2417,c_42])).

cnf(c_2420,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | l1_waybel_0(X0,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2419])).

cnf(c_11034,plain,
    ( ~ m2_yellow_6(X0_59,sK7,X1_59)
    | ~ l1_waybel_0(X1_59,sK7)
    | l1_waybel_0(X0_59,sK7)
    | v2_struct_0(X1_59)
    | ~ v4_orders_2(X1_59)
    | ~ v7_waybel_0(X1_59) ),
    inference(subtyping,[status(esa)],[c_2420])).

cnf(c_11172,plain,
    ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | l1_waybel_0(X0_59,sK7) = iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v4_orders_2(X1_59) != iProver_top
    | v7_waybel_0(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11034])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_542,plain,
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

cnf(c_543,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_2442,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_543,c_40])).

cnf(c_2443,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2442])).

cnf(c_2445,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2443,c_42])).

cnf(c_2446,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_2445])).

cnf(c_11033,plain,
    ( ~ m2_yellow_6(X0_59,sK7,X1_59)
    | ~ l1_waybel_0(X1_59,sK7)
    | v2_struct_0(X1_59)
    | ~ v4_orders_2(X1_59)
    | ~ v7_waybel_0(X1_59)
    | v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_2446])).

cnf(c_11173,plain,
    ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v4_orders_2(X1_59) != iProver_top
    | v7_waybel_0(X1_59) != iProver_top
    | v7_waybel_0(X0_59) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11033])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_514,plain,
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

cnf(c_515,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_2468,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_515,c_40])).

cnf(c_2469,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2468])).

cnf(c_2471,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2469,c_42])).

cnf(c_2472,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2471])).

cnf(c_11032,plain,
    ( ~ m2_yellow_6(X0_59,sK7,X1_59)
    | ~ l1_waybel_0(X1_59,sK7)
    | v2_struct_0(X1_59)
    | ~ v4_orders_2(X1_59)
    | v4_orders_2(X0_59)
    | ~ v7_waybel_0(X1_59) ),
    inference(subtyping,[status(esa)],[c_2472])).

cnf(c_11174,plain,
    ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v4_orders_2(X1_59) != iProver_top
    | v4_orders_2(X0_59) = iProver_top
    | v7_waybel_0(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11032])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_486,plain,
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

cnf(c_487,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_2494,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_487,c_40])).

cnf(c_2495,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2494])).

cnf(c_2497,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2495,c_42])).

cnf(c_2498,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2497])).

cnf(c_11031,plain,
    ( ~ m2_yellow_6(X0_59,sK7,X1_59)
    | ~ l1_waybel_0(X1_59,sK7)
    | ~ v2_struct_0(X0_59)
    | v2_struct_0(X1_59)
    | ~ v4_orders_2(X1_59)
    | ~ v7_waybel_0(X1_59) ),
    inference(subtyping,[status(esa)],[c_2498])).

cnf(c_11175,plain,
    ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | v2_struct_0(X0_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v4_orders_2(X1_59) != iProver_top
    | v7_waybel_0(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11031])).

cnf(c_22691,plain,
    ( v4_orders_2(X1_59) != iProver_top
    | m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | r3_waybel_9(sK7,X1_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
    | k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v7_waybel_0(X1_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21399,c_11172,c_11173,c_11174,c_11175,c_21156])).

cnf(c_22692,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | r3_waybel_9(sK7,X1_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v4_orders_2(X1_59) != iProver_top
    | v7_waybel_0(X1_59) != iProver_top ),
    inference(renaming,[status(thm)],[c_22691])).

cnf(c_25,plain,
    ( ~ r3_waybel_9(X0,sK5(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1731,plain,
    ( ~ r3_waybel_9(X0,sK5(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_41])).

cnf(c_1732,plain,
    ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1731])).

cnf(c_1736,plain,
    ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1732,c_42,c_40])).

cnf(c_11050,plain,
    ( ~ r3_waybel_9(sK7,sK5(sK7),X0_59)
    | ~ m1_subset_1(X0_59,u1_struct_0(sK7))
    | v1_compts_1(sK7) ),
    inference(subtyping,[status(esa)],[c_1736])).

cnf(c_11835,plain,
    ( r3_waybel_9(sK7,sK5(sK7),X0_59) != iProver_top
    | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11050])).

cnf(c_22705,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22692,c_11835])).

cnf(c_30,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK5(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1661,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK5(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_1662,plain,
    ( v1_compts_1(sK7)
    | ~ v2_struct_0(sK5(sK7))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1661])).

cnf(c_1664,plain,
    ( v1_compts_1(sK7)
    | ~ v2_struct_0(sK5(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1662,c_42,c_41,c_40,c_66])).

cnf(c_1666,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1664])).

cnf(c_29,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK5(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1675,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK5(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_1676,plain,
    ( v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | v4_orders_2(sK5(sK7))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1675])).

cnf(c_1678,plain,
    ( v4_orders_2(sK5(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1676,c_42,c_40])).

cnf(c_1679,plain,
    ( v1_compts_1(sK7)
    | v4_orders_2(sK5(sK7)) ),
    inference(renaming,[status(thm)],[c_1678])).

cnf(c_1680,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v4_orders_2(sK5(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1679])).

cnf(c_28,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK5(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1689,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK5(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_41])).

cnf(c_1690,plain,
    ( v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | v7_waybel_0(sK5(sK7))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1689])).

cnf(c_1692,plain,
    ( v7_waybel_0(sK5(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1690,c_42,c_40])).

cnf(c_1693,plain,
    ( v1_compts_1(sK7)
    | v7_waybel_0(sK5(sK7)) ),
    inference(renaming,[status(thm)],[c_1692])).

cnf(c_1694,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v7_waybel_0(sK5(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_27,plain,
    ( l1_waybel_0(sK5(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1703,plain,
    ( l1_waybel_0(sK5(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_41])).

cnf(c_1704,plain,
    ( l1_waybel_0(sK5(sK7),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1703])).

cnf(c_1706,plain,
    ( l1_waybel_0(sK5(sK7),sK7)
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1704,c_42,c_40])).

cnf(c_1708,plain,
    ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1706])).

cnf(c_22807,plain,
    ( v1_compts_1(sK7) = iProver_top
    | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22705,c_1666,c_1680,c_1694,c_1708])).

cnf(c_22808,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_22807])).

cnf(c_22818,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_21156,c_22808])).

cnf(c_12554,plain,
    ( ~ m2_yellow_6(X0_59,sK7,sK5(sK7))
    | ~ l1_waybel_0(sK5(sK7),sK7)
    | v2_struct_0(sK5(sK7))
    | v4_orders_2(X0_59)
    | ~ v4_orders_2(sK5(sK7))
    | ~ v7_waybel_0(sK5(sK7)) ),
    inference(instantiation,[status(thm)],[c_11032])).

cnf(c_12555,plain,
    ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(X0_59) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12554])).

cnf(c_12553,plain,
    ( ~ m2_yellow_6(X0_59,sK7,sK5(sK7))
    | ~ l1_waybel_0(sK5(sK7),sK7)
    | v2_struct_0(sK5(sK7))
    | ~ v4_orders_2(sK5(sK7))
    | v7_waybel_0(X0_59)
    | ~ v7_waybel_0(sK5(sK7)) ),
    inference(instantiation,[status(thm)],[c_11033])).

cnf(c_12559,plain,
    ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(X0_59) = iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12553])).

cnf(c_12552,plain,
    ( ~ m2_yellow_6(X0_59,sK7,sK5(sK7))
    | l1_waybel_0(X0_59,sK7)
    | ~ l1_waybel_0(sK5(sK7),sK7)
    | v2_struct_0(sK5(sK7))
    | ~ v4_orders_2(sK5(sK7))
    | ~ v7_waybel_0(sK5(sK7)) ),
    inference(instantiation,[status(thm)],[c_11034])).

cnf(c_12563,plain,
    ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | l1_waybel_0(X0_59,sK7) = iProver_top
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12552])).

cnf(c_23805,plain,
    ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22818,c_1666,c_1680,c_1694,c_1708,c_12555,c_12559,c_12563,c_21156,c_22808])).

cnf(c_23806,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(renaming,[status(thm)],[c_23805])).

cnf(c_23816,plain,
    ( k10_yellow_6(sK7,sK9(sK5(sK7))) = k1_xboole_0
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK5(sK7))) = iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11824,c_23806])).

cnf(c_11052,plain,
    ( l1_waybel_0(sK5(sK7),sK7)
    | v1_compts_1(sK7) ),
    inference(subtyping,[status(esa)],[c_1706])).

cnf(c_11833,plain,
    ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11052])).

cnf(c_11854,plain,
    ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
    | l1_waybel_0(X1_59,sK7) != iProver_top
    | v2_struct_0(X0_59) != iProver_top
    | v2_struct_0(X1_59) = iProver_top
    | v4_orders_2(X1_59) != iProver_top
    | v7_waybel_0(X1_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11031])).

cnf(c_12498,plain,
    ( l1_waybel_0(X0_59,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(sK9(X0_59)) != iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_11824,c_11854])).

cnf(c_12743,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK5(sK7))) != iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11833,c_12498])).

cnf(c_12908,plain,
    ( v2_struct_0(sK9(sK5(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12743,c_1666,c_1680,c_1694])).

cnf(c_12909,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK5(sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12908])).

cnf(c_1388,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | ~ v2_struct_0(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1)
    | X2 != X0
    | sK9(X2) != X3
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_487,c_39])).

cnf(c_1389,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(X0))
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1388])).

cnf(c_1393,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_42,c_40])).

cnf(c_1394,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1393])).

cnf(c_1358,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
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
    inference(resolution_lifted,[status(thm)],[c_515,c_39])).

cnf(c_1359,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1358])).

cnf(c_1363,plain,
    ( ~ v7_waybel_0(X0)
    | v4_orders_2(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1359,c_42,c_40])).

cnf(c_1364,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1363])).

cnf(c_1328,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
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
    inference(resolution_lifted,[status(thm)],[c_543,c_39])).

cnf(c_1329,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK9(X0))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1328])).

cnf(c_1333,plain,
    ( v7_waybel_0(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_42,c_40])).

cnf(c_1334,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK9(X0)) ),
    inference(renaming,[status(thm)],[c_1333])).

cnf(c_1298,plain,
    ( ~ l1_waybel_0(X0,X1)
    | l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X3)
    | ~ l1_pre_topc(X1)
    | X3 != X0
    | sK9(X3) != X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_571,c_39])).

cnf(c_1299,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1303,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_42,c_40])).

cnf(c_1304,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1303])).

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
    inference(cnf_transformation,[],[f82])).

cnf(c_38,negated_conjecture,
    ( v3_yellow_6(sK9(X0),sK7)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_668,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0
    | sK9(X2) != X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_38])).

cnf(c_669,plain,
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
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_673,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_42,c_41,c_40])).

cnf(c_674,plain,
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
    inference(renaming,[status(thm)],[c_673])).

cnf(c_1574,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK9(X0))
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1304,c_674])).

cnf(c_1588,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1334,c_1574])).

cnf(c_1597,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1364,c_1588])).

cnf(c_1606,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1394,c_1597])).

cnf(c_11057,plain,
    ( ~ l1_waybel_0(X0_59,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | k10_yellow_6(sK7,sK9(X0_59)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1606])).

cnf(c_12945,plain,
    ( ~ l1_waybel_0(sK5(sK7),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK5(sK7))
    | ~ v4_orders_2(sK5(sK7))
    | ~ v7_waybel_0(sK5(sK7))
    | k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11057])).

cnf(c_12946,plain,
    ( k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0
    | l1_waybel_0(sK5(sK7),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK5(sK7)) = iProver_top
    | v4_orders_2(sK5(sK7)) != iProver_top
    | v7_waybel_0(sK5(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12945])).

cnf(c_23842,plain,
    ( v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23816,c_1666,c_1680,c_1694,c_1708,c_12909,c_12946])).

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
    inference(cnf_transformation,[],[f89])).

cnf(c_1752,plain,
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

cnf(c_1753,plain,
    ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1752])).

cnf(c_1757,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1753,c_42,c_40])).

cnf(c_1758,plain,
    ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1757])).

cnf(c_11049,plain,
    ( r3_waybel_9(sK7,X0_59,sK4(sK7,X0_59))
    | ~ l1_waybel_0(X0_59,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1758])).

cnf(c_11836,plain,
    ( r3_waybel_9(sK7,X0_59,sK4(sK7,X0_59)) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11049])).

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
    inference(cnf_transformation,[],[f86])).

cnf(c_1782,plain,
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

cnf(c_1783,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1782])).

cnf(c_1787,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1783,c_42,c_40])).

cnf(c_1788,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1787])).

cnf(c_11048,plain,
    ( ~ r3_waybel_9(sK7,X0_59,X1_59)
    | m2_yellow_6(sK3(sK7,X0_59,X1_59),sK7,X0_59)
    | ~ l1_waybel_0(X0_59,sK7)
    | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1788])).

cnf(c_11837,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
    | m2_yellow_6(sK3(sK7,X0_59,X1_59),sK7,X0_59) = iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11048])).

cnf(c_13386,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v2_struct_0(sK3(sK7,X0_59,X1_59)) != iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(superposition,[status(thm)],[c_11837,c_11854])).

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
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ v3_yellow_6(X0,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_635,plain,
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

cnf(c_636,plain,
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
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_640,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m2_yellow_6(X0,sK7,sK8)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_636,c_42,c_41,c_40])).

cnf(c_641,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_640])).

cnf(c_11058,plain,
    ( ~ m2_yellow_6(X0_59,sK7,sK8)
    | ~ l1_waybel_0(X0_59,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59)
    | k10_yellow_6(sK7,X0_59) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_641])).

cnf(c_11827,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK8) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11058])).

cnf(c_37,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_52,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_53,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v4_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_54,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v7_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_55,plain,
    ( l1_waybel_0(sK8,sK7) = iProver_top
    | v1_compts_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11134,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK8) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11058])).

cnf(c_12328,plain,
    ( ~ m2_yellow_6(X0_59,sK7,sK8)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | v4_orders_2(X0_59)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11032])).

cnf(c_12329,plain,
    ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(X0_59) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12328])).

cnf(c_12333,plain,
    ( ~ m2_yellow_6(X0_59,sK7,sK8)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | v7_waybel_0(X0_59)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11033])).

cnf(c_12334,plain,
    ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(X0_59) = iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12333])).

cnf(c_12344,plain,
    ( ~ m2_yellow_6(X0_59,sK7,sK8)
    | l1_waybel_0(X0_59,sK7)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11034])).

cnf(c_12345,plain,
    ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
    | l1_waybel_0(X0_59,sK7) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12344])).

cnf(c_12440,plain,
    ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
    | k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11827,c_52,c_53,c_54,c_55,c_11134,c_12329,c_12334,c_12345])).

cnf(c_12441,plain,
    ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
    | m2_yellow_6(X0_59,sK7,sK8) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0_59) = iProver_top ),
    inference(renaming,[status(thm)],[c_12440])).

cnf(c_13387,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0_59) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK3(sK7,sK8,X0_59)) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11837,c_12441])).

cnf(c_13418,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0_59) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_13386,c_13387])).

cnf(c_14719,plain,
    ( v1_compts_1(sK7) != iProver_top
    | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
    | k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0_59) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13418,c_52,c_53,c_54,c_55])).

cnf(c_14720,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0_59) != iProver_top
    | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_14719])).

cnf(c_14729,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11836,c_14720])).

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
    inference(cnf_transformation,[],[f88])).

cnf(c_2090,plain,
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

cnf(c_2091,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_2090])).

cnf(c_2095,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2091,c_42,c_40])).

cnf(c_2096,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_2095])).

cnf(c_11041,plain,
    ( ~ l1_waybel_0(X0_59,sK7)
    | m1_subset_1(sK4(sK7,X0_59),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_2096])).

cnf(c_12316,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11041])).

cnf(c_12317,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12316])).

cnf(c_14907,plain,
    ( v1_compts_1(sK7) != iProver_top
    | k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14729,c_52,c_53,c_54,c_55,c_12317])).

cnf(c_14908,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
    | v1_compts_1(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_14907])).

cnf(c_23847,plain,
    ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23842,c_14908])).

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
    inference(cnf_transformation,[],[f87])).

cnf(c_1815,plain,
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

cnf(c_1816,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1815])).

cnf(c_1820,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1816,c_42,c_40])).

cnf(c_1821,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1820])).

cnf(c_11047,plain,
    ( ~ r3_waybel_9(sK7,X0_59,X1_59)
    | ~ l1_waybel_0(X0_59,sK7)
    | r2_hidden(X1_59,k10_yellow_6(sK7,sK3(sK7,X0_59,X1_59)))
    | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
    | v2_struct_0(X0_59)
    | ~ v4_orders_2(X0_59)
    | ~ v7_waybel_0(X0_59) ),
    inference(subtyping,[status(esa)],[c_1821])).

cnf(c_11838,plain,
    ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
    | l1_waybel_0(X0_59,sK7) != iProver_top
    | r2_hidden(X1_59,k10_yellow_6(sK7,sK3(sK7,X0_59,X1_59))) = iProver_top
    | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0_59) = iProver_top
    | v4_orders_2(X0_59) != iProver_top
    | v7_waybel_0(X0_59) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11047])).

cnf(c_24032,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top
    | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_23847,c_11838])).

cnf(c_12322,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_11049])).

cnf(c_12323,plain,
    ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12322])).

cnf(c_24428,plain,
    ( r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24032,c_52,c_53,c_54,c_55,c_1666,c_1680,c_1694,c_1708,c_12317,c_12323,c_12909,c_12946,c_23816])).

cnf(c_24433,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24428,c_11826])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.37/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.37/1.49  
% 7.37/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.37/1.49  
% 7.37/1.49  ------  iProver source info
% 7.37/1.49  
% 7.37/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.37/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.37/1.49  git: non_committed_changes: false
% 7.37/1.49  git: last_make_outside_of_git: false
% 7.37/1.49  
% 7.37/1.49  ------ 
% 7.37/1.49  
% 7.37/1.49  ------ Input Options
% 7.37/1.49  
% 7.37/1.49  --out_options                           all
% 7.37/1.49  --tptp_safe_out                         true
% 7.37/1.49  --problem_path                          ""
% 7.37/1.49  --include_path                          ""
% 7.37/1.49  --clausifier                            res/vclausify_rel
% 7.37/1.49  --clausifier_options                    --mode clausify
% 7.37/1.49  --stdin                                 false
% 7.37/1.49  --stats_out                             all
% 7.37/1.49  
% 7.37/1.49  ------ General Options
% 7.37/1.49  
% 7.37/1.49  --fof                                   false
% 7.37/1.49  --time_out_real                         305.
% 7.37/1.49  --time_out_virtual                      -1.
% 7.37/1.49  --symbol_type_check                     false
% 7.37/1.49  --clausify_out                          false
% 7.37/1.49  --sig_cnt_out                           false
% 7.37/1.49  --trig_cnt_out                          false
% 7.37/1.49  --trig_cnt_out_tolerance                1.
% 7.37/1.49  --trig_cnt_out_sk_spl                   false
% 7.37/1.49  --abstr_cl_out                          false
% 7.37/1.49  
% 7.37/1.49  ------ Global Options
% 7.37/1.49  
% 7.37/1.49  --schedule                              default
% 7.37/1.49  --add_important_lit                     false
% 7.37/1.49  --prop_solver_per_cl                    1000
% 7.37/1.49  --min_unsat_core                        false
% 7.37/1.49  --soft_assumptions                      false
% 7.37/1.49  --soft_lemma_size                       3
% 7.37/1.49  --prop_impl_unit_size                   0
% 7.37/1.49  --prop_impl_unit                        []
% 7.37/1.49  --share_sel_clauses                     true
% 7.37/1.49  --reset_solvers                         false
% 7.37/1.49  --bc_imp_inh                            [conj_cone]
% 7.37/1.49  --conj_cone_tolerance                   3.
% 7.37/1.49  --extra_neg_conj                        none
% 7.37/1.49  --large_theory_mode                     true
% 7.37/1.49  --prolific_symb_bound                   200
% 7.37/1.49  --lt_threshold                          2000
% 7.37/1.49  --clause_weak_htbl                      true
% 7.37/1.49  --gc_record_bc_elim                     false
% 7.37/1.49  
% 7.37/1.49  ------ Preprocessing Options
% 7.37/1.49  
% 7.37/1.49  --preprocessing_flag                    true
% 7.37/1.49  --time_out_prep_mult                    0.1
% 7.37/1.49  --splitting_mode                        input
% 7.37/1.49  --splitting_grd                         true
% 7.37/1.49  --splitting_cvd                         false
% 7.37/1.49  --splitting_cvd_svl                     false
% 7.37/1.49  --splitting_nvd                         32
% 7.37/1.49  --sub_typing                            true
% 7.37/1.49  --prep_gs_sim                           true
% 7.37/1.49  --prep_unflatten                        true
% 7.37/1.49  --prep_res_sim                          true
% 7.37/1.49  --prep_upred                            true
% 7.37/1.49  --prep_sem_filter                       exhaustive
% 7.37/1.49  --prep_sem_filter_out                   false
% 7.37/1.49  --pred_elim                             true
% 7.37/1.49  --res_sim_input                         true
% 7.37/1.49  --eq_ax_congr_red                       true
% 7.37/1.49  --pure_diseq_elim                       true
% 7.37/1.49  --brand_transform                       false
% 7.37/1.49  --non_eq_to_eq                          false
% 7.37/1.49  --prep_def_merge                        true
% 7.37/1.49  --prep_def_merge_prop_impl              false
% 7.37/1.49  --prep_def_merge_mbd                    true
% 7.37/1.49  --prep_def_merge_tr_red                 false
% 7.37/1.49  --prep_def_merge_tr_cl                  false
% 7.37/1.49  --smt_preprocessing                     true
% 7.37/1.49  --smt_ac_axioms                         fast
% 7.37/1.49  --preprocessed_out                      false
% 7.37/1.49  --preprocessed_stats                    false
% 7.37/1.49  
% 7.37/1.49  ------ Abstraction refinement Options
% 7.37/1.49  
% 7.37/1.49  --abstr_ref                             []
% 7.37/1.49  --abstr_ref_prep                        false
% 7.37/1.49  --abstr_ref_until_sat                   false
% 7.37/1.49  --abstr_ref_sig_restrict                funpre
% 7.37/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.49  --abstr_ref_under                       []
% 7.37/1.49  
% 7.37/1.49  ------ SAT Options
% 7.37/1.49  
% 7.37/1.49  --sat_mode                              false
% 7.37/1.49  --sat_fm_restart_options                ""
% 7.37/1.49  --sat_gr_def                            false
% 7.37/1.49  --sat_epr_types                         true
% 7.37/1.49  --sat_non_cyclic_types                  false
% 7.37/1.49  --sat_finite_models                     false
% 7.37/1.49  --sat_fm_lemmas                         false
% 7.37/1.49  --sat_fm_prep                           false
% 7.37/1.49  --sat_fm_uc_incr                        true
% 7.37/1.49  --sat_out_model                         small
% 7.37/1.49  --sat_out_clauses                       false
% 7.37/1.49  
% 7.37/1.49  ------ QBF Options
% 7.37/1.49  
% 7.37/1.49  --qbf_mode                              false
% 7.37/1.49  --qbf_elim_univ                         false
% 7.37/1.49  --qbf_dom_inst                          none
% 7.37/1.49  --qbf_dom_pre_inst                      false
% 7.37/1.49  --qbf_sk_in                             false
% 7.37/1.49  --qbf_pred_elim                         true
% 7.37/1.49  --qbf_split                             512
% 7.37/1.49  
% 7.37/1.49  ------ BMC1 Options
% 7.37/1.49  
% 7.37/1.49  --bmc1_incremental                      false
% 7.37/1.49  --bmc1_axioms                           reachable_all
% 7.37/1.49  --bmc1_min_bound                        0
% 7.37/1.49  --bmc1_max_bound                        -1
% 7.37/1.49  --bmc1_max_bound_default                -1
% 7.37/1.49  --bmc1_symbol_reachability              true
% 7.37/1.49  --bmc1_property_lemmas                  false
% 7.37/1.49  --bmc1_k_induction                      false
% 7.37/1.49  --bmc1_non_equiv_states                 false
% 7.37/1.49  --bmc1_deadlock                         false
% 7.37/1.49  --bmc1_ucm                              false
% 7.37/1.49  --bmc1_add_unsat_core                   none
% 7.37/1.49  --bmc1_unsat_core_children              false
% 7.37/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.49  --bmc1_out_stat                         full
% 7.37/1.49  --bmc1_ground_init                      false
% 7.37/1.49  --bmc1_pre_inst_next_state              false
% 7.37/1.49  --bmc1_pre_inst_state                   false
% 7.37/1.49  --bmc1_pre_inst_reach_state             false
% 7.37/1.49  --bmc1_out_unsat_core                   false
% 7.37/1.49  --bmc1_aig_witness_out                  false
% 7.37/1.49  --bmc1_verbose                          false
% 7.37/1.49  --bmc1_dump_clauses_tptp                false
% 7.37/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.49  --bmc1_dump_file                        -
% 7.37/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.49  --bmc1_ucm_extend_mode                  1
% 7.37/1.49  --bmc1_ucm_init_mode                    2
% 7.37/1.49  --bmc1_ucm_cone_mode                    none
% 7.37/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.49  --bmc1_ucm_relax_model                  4
% 7.37/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.49  --bmc1_ucm_layered_model                none
% 7.37/1.49  --bmc1_ucm_max_lemma_size               10
% 7.37/1.49  
% 7.37/1.49  ------ AIG Options
% 7.37/1.49  
% 7.37/1.49  --aig_mode                              false
% 7.37/1.49  
% 7.37/1.49  ------ Instantiation Options
% 7.37/1.49  
% 7.37/1.49  --instantiation_flag                    true
% 7.37/1.49  --inst_sos_flag                         false
% 7.37/1.49  --inst_sos_phase                        true
% 7.37/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.49  --inst_lit_sel_side                     num_symb
% 7.37/1.49  --inst_solver_per_active                1400
% 7.37/1.49  --inst_solver_calls_frac                1.
% 7.37/1.49  --inst_passive_queue_type               priority_queues
% 7.37/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.49  --inst_passive_queues_freq              [25;2]
% 7.37/1.49  --inst_dismatching                      true
% 7.37/1.49  --inst_eager_unprocessed_to_passive     true
% 7.37/1.49  --inst_prop_sim_given                   true
% 7.37/1.49  --inst_prop_sim_new                     false
% 7.37/1.49  --inst_subs_new                         false
% 7.37/1.49  --inst_eq_res_simp                      false
% 7.37/1.49  --inst_subs_given                       false
% 7.37/1.49  --inst_orphan_elimination               true
% 7.37/1.49  --inst_learning_loop_flag               true
% 7.37/1.49  --inst_learning_start                   3000
% 7.37/1.49  --inst_learning_factor                  2
% 7.37/1.49  --inst_start_prop_sim_after_learn       3
% 7.37/1.49  --inst_sel_renew                        solver
% 7.37/1.49  --inst_lit_activity_flag                true
% 7.37/1.49  --inst_restr_to_given                   false
% 7.37/1.49  --inst_activity_threshold               500
% 7.37/1.49  --inst_out_proof                        true
% 7.37/1.49  
% 7.37/1.49  ------ Resolution Options
% 7.37/1.49  
% 7.37/1.49  --resolution_flag                       true
% 7.37/1.49  --res_lit_sel                           adaptive
% 7.37/1.49  --res_lit_sel_side                      none
% 7.37/1.49  --res_ordering                          kbo
% 7.37/1.49  --res_to_prop_solver                    active
% 7.37/1.49  --res_prop_simpl_new                    false
% 7.37/1.49  --res_prop_simpl_given                  true
% 7.37/1.49  --res_passive_queue_type                priority_queues
% 7.37/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.49  --res_passive_queues_freq               [15;5]
% 7.37/1.49  --res_forward_subs                      full
% 7.37/1.49  --res_backward_subs                     full
% 7.37/1.49  --res_forward_subs_resolution           true
% 7.37/1.49  --res_backward_subs_resolution          true
% 7.37/1.49  --res_orphan_elimination                true
% 7.37/1.49  --res_time_limit                        2.
% 7.37/1.49  --res_out_proof                         true
% 7.37/1.49  
% 7.37/1.49  ------ Superposition Options
% 7.37/1.49  
% 7.37/1.49  --superposition_flag                    true
% 7.37/1.49  --sup_passive_queue_type                priority_queues
% 7.37/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.49  --demod_completeness_check              fast
% 7.37/1.49  --demod_use_ground                      true
% 7.37/1.49  --sup_to_prop_solver                    passive
% 7.37/1.49  --sup_prop_simpl_new                    true
% 7.37/1.49  --sup_prop_simpl_given                  true
% 7.37/1.49  --sup_fun_splitting                     false
% 7.37/1.49  --sup_smt_interval                      50000
% 7.37/1.49  
% 7.37/1.49  ------ Superposition Simplification Setup
% 7.37/1.49  
% 7.37/1.49  --sup_indices_passive                   []
% 7.37/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.49  --sup_full_bw                           [BwDemod]
% 7.37/1.49  --sup_immed_triv                        [TrivRules]
% 7.37/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.49  --sup_immed_bw_main                     []
% 7.37/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.49  
% 7.37/1.49  ------ Combination Options
% 7.37/1.49  
% 7.37/1.49  --comb_res_mult                         3
% 7.37/1.49  --comb_sup_mult                         2
% 7.37/1.49  --comb_inst_mult                        10
% 7.37/1.49  
% 7.37/1.49  ------ Debug Options
% 7.37/1.49  
% 7.37/1.49  --dbg_backtrace                         false
% 7.37/1.49  --dbg_dump_prop_clauses                 false
% 7.37/1.49  --dbg_dump_prop_clauses_file            -
% 7.37/1.49  --dbg_out_stat                          false
% 7.37/1.49  ------ Parsing...
% 7.37/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.37/1.49  
% 7.37/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.37/1.49  
% 7.37/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.37/1.49  
% 7.37/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.37/1.49  ------ Proving...
% 7.37/1.49  ------ Problem Properties 
% 7.37/1.49  
% 7.37/1.49  
% 7.37/1.49  clauses                                 37
% 7.37/1.49  conjectures                             6
% 7.37/1.49  EPR                                     10
% 7.37/1.49  Horn                                    11
% 7.37/1.49  unary                                   3
% 7.37/1.49  binary                                  9
% 7.37/1.49  lits                                    184
% 7.37/1.49  lits eq                                 6
% 7.37/1.49  fd_pure                                 0
% 7.37/1.49  fd_pseudo                               0
% 7.37/1.49  fd_cond                                 0
% 7.37/1.49  fd_pseudo_cond                          4
% 7.37/1.49  AC symbols                              0
% 7.37/1.49  
% 7.37/1.49  ------ Schedule dynamic 5 is on 
% 7.37/1.49  
% 7.37/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.37/1.49  
% 7.37/1.49  
% 7.37/1.49  ------ 
% 7.37/1.49  Current options:
% 7.37/1.49  ------ 
% 7.37/1.49  
% 7.37/1.49  ------ Input Options
% 7.37/1.49  
% 7.37/1.49  --out_options                           all
% 7.37/1.49  --tptp_safe_out                         true
% 7.37/1.49  --problem_path                          ""
% 7.37/1.49  --include_path                          ""
% 7.37/1.49  --clausifier                            res/vclausify_rel
% 7.37/1.49  --clausifier_options                    --mode clausify
% 7.37/1.49  --stdin                                 false
% 7.37/1.49  --stats_out                             all
% 7.37/1.49  
% 7.37/1.49  ------ General Options
% 7.37/1.49  
% 7.37/1.49  --fof                                   false
% 7.37/1.49  --time_out_real                         305.
% 7.37/1.49  --time_out_virtual                      -1.
% 7.37/1.49  --symbol_type_check                     false
% 7.37/1.49  --clausify_out                          false
% 7.37/1.49  --sig_cnt_out                           false
% 7.37/1.49  --trig_cnt_out                          false
% 7.37/1.49  --trig_cnt_out_tolerance                1.
% 7.37/1.49  --trig_cnt_out_sk_spl                   false
% 7.37/1.49  --abstr_cl_out                          false
% 7.37/1.49  
% 7.37/1.49  ------ Global Options
% 7.37/1.49  
% 7.37/1.49  --schedule                              default
% 7.37/1.49  --add_important_lit                     false
% 7.37/1.49  --prop_solver_per_cl                    1000
% 7.37/1.49  --min_unsat_core                        false
% 7.37/1.49  --soft_assumptions                      false
% 7.37/1.49  --soft_lemma_size                       3
% 7.37/1.49  --prop_impl_unit_size                   0
% 7.37/1.49  --prop_impl_unit                        []
% 7.37/1.49  --share_sel_clauses                     true
% 7.37/1.49  --reset_solvers                         false
% 7.37/1.49  --bc_imp_inh                            [conj_cone]
% 7.37/1.49  --conj_cone_tolerance                   3.
% 7.37/1.49  --extra_neg_conj                        none
% 7.37/1.49  --large_theory_mode                     true
% 7.37/1.49  --prolific_symb_bound                   200
% 7.37/1.49  --lt_threshold                          2000
% 7.37/1.49  --clause_weak_htbl                      true
% 7.37/1.49  --gc_record_bc_elim                     false
% 7.37/1.49  
% 7.37/1.49  ------ Preprocessing Options
% 7.37/1.49  
% 7.37/1.49  --preprocessing_flag                    true
% 7.37/1.49  --time_out_prep_mult                    0.1
% 7.37/1.49  --splitting_mode                        input
% 7.37/1.49  --splitting_grd                         true
% 7.37/1.49  --splitting_cvd                         false
% 7.37/1.49  --splitting_cvd_svl                     false
% 7.37/1.49  --splitting_nvd                         32
% 7.37/1.49  --sub_typing                            true
% 7.37/1.49  --prep_gs_sim                           true
% 7.37/1.49  --prep_unflatten                        true
% 7.37/1.49  --prep_res_sim                          true
% 7.37/1.49  --prep_upred                            true
% 7.37/1.49  --prep_sem_filter                       exhaustive
% 7.37/1.49  --prep_sem_filter_out                   false
% 7.37/1.49  --pred_elim                             true
% 7.37/1.49  --res_sim_input                         true
% 7.37/1.49  --eq_ax_congr_red                       true
% 7.37/1.49  --pure_diseq_elim                       true
% 7.37/1.49  --brand_transform                       false
% 7.37/1.49  --non_eq_to_eq                          false
% 7.37/1.49  --prep_def_merge                        true
% 7.37/1.49  --prep_def_merge_prop_impl              false
% 7.37/1.49  --prep_def_merge_mbd                    true
% 7.37/1.49  --prep_def_merge_tr_red                 false
% 7.37/1.49  --prep_def_merge_tr_cl                  false
% 7.37/1.49  --smt_preprocessing                     true
% 7.37/1.49  --smt_ac_axioms                         fast
% 7.37/1.49  --preprocessed_out                      false
% 7.37/1.49  --preprocessed_stats                    false
% 7.37/1.49  
% 7.37/1.49  ------ Abstraction refinement Options
% 7.37/1.49  
% 7.37/1.49  --abstr_ref                             []
% 7.37/1.49  --abstr_ref_prep                        false
% 7.37/1.49  --abstr_ref_until_sat                   false
% 7.37/1.49  --abstr_ref_sig_restrict                funpre
% 7.37/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.49  --abstr_ref_under                       []
% 7.37/1.49  
% 7.37/1.49  ------ SAT Options
% 7.37/1.49  
% 7.37/1.49  --sat_mode                              false
% 7.37/1.49  --sat_fm_restart_options                ""
% 7.37/1.49  --sat_gr_def                            false
% 7.37/1.49  --sat_epr_types                         true
% 7.37/1.49  --sat_non_cyclic_types                  false
% 7.37/1.49  --sat_finite_models                     false
% 7.37/1.49  --sat_fm_lemmas                         false
% 7.37/1.49  --sat_fm_prep                           false
% 7.37/1.49  --sat_fm_uc_incr                        true
% 7.37/1.49  --sat_out_model                         small
% 7.37/1.49  --sat_out_clauses                       false
% 7.37/1.49  
% 7.37/1.49  ------ QBF Options
% 7.37/1.49  
% 7.37/1.49  --qbf_mode                              false
% 7.37/1.49  --qbf_elim_univ                         false
% 7.37/1.49  --qbf_dom_inst                          none
% 7.37/1.49  --qbf_dom_pre_inst                      false
% 7.37/1.49  --qbf_sk_in                             false
% 7.37/1.49  --qbf_pred_elim                         true
% 7.37/1.49  --qbf_split                             512
% 7.37/1.49  
% 7.37/1.49  ------ BMC1 Options
% 7.37/1.49  
% 7.37/1.49  --bmc1_incremental                      false
% 7.37/1.49  --bmc1_axioms                           reachable_all
% 7.37/1.49  --bmc1_min_bound                        0
% 7.37/1.49  --bmc1_max_bound                        -1
% 7.37/1.49  --bmc1_max_bound_default                -1
% 7.37/1.49  --bmc1_symbol_reachability              true
% 7.37/1.49  --bmc1_property_lemmas                  false
% 7.37/1.49  --bmc1_k_induction                      false
% 7.37/1.49  --bmc1_non_equiv_states                 false
% 7.37/1.49  --bmc1_deadlock                         false
% 7.37/1.49  --bmc1_ucm                              false
% 7.37/1.49  --bmc1_add_unsat_core                   none
% 7.37/1.49  --bmc1_unsat_core_children              false
% 7.37/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.49  --bmc1_out_stat                         full
% 7.37/1.49  --bmc1_ground_init                      false
% 7.37/1.49  --bmc1_pre_inst_next_state              false
% 7.37/1.49  --bmc1_pre_inst_state                   false
% 7.37/1.49  --bmc1_pre_inst_reach_state             false
% 7.37/1.49  --bmc1_out_unsat_core                   false
% 7.37/1.49  --bmc1_aig_witness_out                  false
% 7.37/1.49  --bmc1_verbose                          false
% 7.37/1.49  --bmc1_dump_clauses_tptp                false
% 7.37/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.49  --bmc1_dump_file                        -
% 7.37/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.49  --bmc1_ucm_extend_mode                  1
% 7.37/1.49  --bmc1_ucm_init_mode                    2
% 7.37/1.49  --bmc1_ucm_cone_mode                    none
% 7.37/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.49  --bmc1_ucm_relax_model                  4
% 7.37/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.49  --bmc1_ucm_layered_model                none
% 7.37/1.49  --bmc1_ucm_max_lemma_size               10
% 7.37/1.49  
% 7.37/1.49  ------ AIG Options
% 7.37/1.49  
% 7.37/1.49  --aig_mode                              false
% 7.37/1.49  
% 7.37/1.49  ------ Instantiation Options
% 7.37/1.49  
% 7.37/1.49  --instantiation_flag                    true
% 7.37/1.49  --inst_sos_flag                         false
% 7.37/1.49  --inst_sos_phase                        true
% 7.37/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.49  --inst_lit_sel_side                     none
% 7.37/1.49  --inst_solver_per_active                1400
% 7.37/1.49  --inst_solver_calls_frac                1.
% 7.37/1.49  --inst_passive_queue_type               priority_queues
% 7.37/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.49  --inst_passive_queues_freq              [25;2]
% 7.37/1.49  --inst_dismatching                      true
% 7.37/1.49  --inst_eager_unprocessed_to_passive     true
% 7.37/1.49  --inst_prop_sim_given                   true
% 7.37/1.49  --inst_prop_sim_new                     false
% 7.37/1.49  --inst_subs_new                         false
% 7.37/1.49  --inst_eq_res_simp                      false
% 7.37/1.49  --inst_subs_given                       false
% 7.37/1.49  --inst_orphan_elimination               true
% 7.37/1.49  --inst_learning_loop_flag               true
% 7.37/1.49  --inst_learning_start                   3000
% 7.37/1.49  --inst_learning_factor                  2
% 7.37/1.49  --inst_start_prop_sim_after_learn       3
% 7.37/1.49  --inst_sel_renew                        solver
% 7.37/1.49  --inst_lit_activity_flag                true
% 7.37/1.49  --inst_restr_to_given                   false
% 7.37/1.49  --inst_activity_threshold               500
% 7.37/1.49  --inst_out_proof                        true
% 7.37/1.49  
% 7.37/1.49  ------ Resolution Options
% 7.37/1.49  
% 7.37/1.49  --resolution_flag                       false
% 7.37/1.49  --res_lit_sel                           adaptive
% 7.37/1.49  --res_lit_sel_side                      none
% 7.37/1.49  --res_ordering                          kbo
% 7.37/1.49  --res_to_prop_solver                    active
% 7.37/1.49  --res_prop_simpl_new                    false
% 7.37/1.49  --res_prop_simpl_given                  true
% 7.37/1.49  --res_passive_queue_type                priority_queues
% 7.37/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.49  --res_passive_queues_freq               [15;5]
% 7.37/1.49  --res_forward_subs                      full
% 7.37/1.49  --res_backward_subs                     full
% 7.37/1.49  --res_forward_subs_resolution           true
% 7.37/1.49  --res_backward_subs_resolution          true
% 7.37/1.49  --res_orphan_elimination                true
% 7.37/1.49  --res_time_limit                        2.
% 7.37/1.49  --res_out_proof                         true
% 7.37/1.49  
% 7.37/1.49  ------ Superposition Options
% 7.37/1.49  
% 7.37/1.49  --superposition_flag                    true
% 7.37/1.49  --sup_passive_queue_type                priority_queues
% 7.37/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.49  --demod_completeness_check              fast
% 7.37/1.49  --demod_use_ground                      true
% 7.37/1.49  --sup_to_prop_solver                    passive
% 7.37/1.49  --sup_prop_simpl_new                    true
% 7.37/1.49  --sup_prop_simpl_given                  true
% 7.37/1.49  --sup_fun_splitting                     false
% 7.37/1.49  --sup_smt_interval                      50000
% 7.37/1.49  
% 7.37/1.49  ------ Superposition Simplification Setup
% 7.37/1.49  
% 7.37/1.49  --sup_indices_passive                   []
% 7.37/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.49  --sup_full_bw                           [BwDemod]
% 7.37/1.49  --sup_immed_triv                        [TrivRules]
% 7.37/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.49  --sup_immed_bw_main                     []
% 7.37/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.49  
% 7.37/1.49  ------ Combination Options
% 7.37/1.49  
% 7.37/1.49  --comb_res_mult                         3
% 7.37/1.49  --comb_sup_mult                         2
% 7.37/1.49  --comb_inst_mult                        10
% 7.37/1.49  
% 7.37/1.49  ------ Debug Options
% 7.37/1.49  
% 7.37/1.49  --dbg_backtrace                         false
% 7.37/1.49  --dbg_dump_prop_clauses                 false
% 7.37/1.49  --dbg_dump_prop_clauses_file            -
% 7.37/1.49  --dbg_out_stat                          false
% 7.37/1.49  
% 7.37/1.49  
% 7.37/1.49  
% 7.37/1.49  
% 7.37/1.49  ------ Proving...
% 7.37/1.49  
% 7.37/1.49  
% 7.37/1.49  % SZS status Theorem for theBenchmark.p
% 7.37/1.49  
% 7.37/1.49   Resolution empty clause
% 7.37/1.49  
% 7.37/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.37/1.49  
% 7.37/1.49  fof(f15,conjecture,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f16,negated_conjecture,(
% 7.37/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 7.37/1.49    inference(negated_conjecture,[],[f15])).
% 7.37/1.49  
% 7.37/1.49  fof(f39,plain,(
% 7.37/1.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f16])).
% 7.37/1.49  
% 7.37/1.49  fof(f40,plain,(
% 7.37/1.49    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f39])).
% 7.37/1.49  
% 7.37/1.49  fof(f58,plain,(
% 7.37/1.49    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.37/1.49    inference(nnf_transformation,[],[f40])).
% 7.37/1.49  
% 7.37/1.49  fof(f59,plain,(
% 7.37/1.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f58])).
% 7.37/1.49  
% 7.37/1.49  fof(f60,plain,(
% 7.37/1.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.37/1.49    inference(rectify,[],[f59])).
% 7.37/1.49  
% 7.37/1.49  fof(f63,plain,(
% 7.37/1.49    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK9(X3),X0) & m2_yellow_6(sK9(X3),X0,X3)))) )),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f62,plain,(
% 7.37/1.49    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK8)) & l1_waybel_0(sK8,X0) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8))) )),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f61,plain,(
% 7.37/1.49    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,X1)) & l1_waybel_0(X1,sK7) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK7)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK7) & m2_yellow_6(X4,sK7,X3)) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7))),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f64,plain,(
% 7.37/1.49    ((! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,sK8)) & l1_waybel_0(sK8,sK7) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8)) | ~v1_compts_1(sK7)) & (! [X3] : ((v3_yellow_6(sK9(X3),sK7) & m2_yellow_6(sK9(X3),sK7,X3)) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7)),
% 7.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f60,f63,f62,f61])).
% 7.37/1.49  
% 7.37/1.49  fof(f101,plain,(
% 7.37/1.49    ( ! [X3] : (m2_yellow_6(sK9(X3),sK7,X3) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK7)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f7,axiom,(
% 7.37/1.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f23,plain,(
% 7.37/1.49    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f7])).
% 7.37/1.49  
% 7.37/1.49  fof(f24,plain,(
% 7.37/1.49    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f23])).
% 7.37/1.49  
% 7.37/1.49  fof(f77,plain,(
% 7.37/1.49    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f24])).
% 7.37/1.49  
% 7.37/1.49  fof(f99,plain,(
% 7.37/1.49    v2_pre_topc(sK7)),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f98,plain,(
% 7.37/1.49    ~v2_struct_0(sK7)),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f100,plain,(
% 7.37/1.49    l1_pre_topc(sK7)),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f6,axiom,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f21,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f6])).
% 7.37/1.49  
% 7.37/1.49  fof(f22,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f21])).
% 7.37/1.49  
% 7.37/1.49  fof(f41,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(nnf_transformation,[],[f22])).
% 7.37/1.49  
% 7.37/1.49  fof(f42,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f41])).
% 7.37/1.49  
% 7.37/1.49  fof(f43,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(rectify,[],[f42])).
% 7.37/1.49  
% 7.37/1.49  fof(f46,plain,(
% 7.37/1.49    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6)))),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f45,plain,(
% 7.37/1.49    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X3)))) )),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f44,plain,(
% 7.37/1.49    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f47,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).
% 7.37/1.49  
% 7.37/1.49  fof(f71,plain,(
% 7.37/1.49    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f47])).
% 7.37/1.49  
% 7.37/1.49  fof(f109,plain,(
% 7.37/1.49    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(equality_resolution,[],[f71])).
% 7.37/1.49  
% 7.37/1.49  fof(f74,plain,(
% 7.37/1.49    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2)) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f47])).
% 7.37/1.49  
% 7.37/1.49  fof(f73,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f47])).
% 7.37/1.49  
% 7.37/1.49  fof(f72,plain,(
% 7.37/1.49    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f47])).
% 7.37/1.49  
% 7.37/1.49  fof(f108,plain,(
% 7.37/1.49    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(equality_resolution,[],[f72])).
% 7.37/1.49  
% 7.37/1.49  fof(f1,axiom,(
% 7.37/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f65,plain,(
% 7.37/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f1])).
% 7.37/1.49  
% 7.37/1.49  fof(f4,axiom,(
% 7.37/1.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f19,plain,(
% 7.37/1.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.37/1.49    inference(ennf_transformation,[],[f4])).
% 7.37/1.49  
% 7.37/1.49  fof(f68,plain,(
% 7.37/1.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f19])).
% 7.37/1.49  
% 7.37/1.49  fof(f2,axiom,(
% 7.37/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f66,plain,(
% 7.37/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.37/1.49    inference(cnf_transformation,[],[f2])).
% 7.37/1.49  
% 7.37/1.49  fof(f3,axiom,(
% 7.37/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f17,plain,(
% 7.37/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.37/1.49    inference(ennf_transformation,[],[f3])).
% 7.37/1.49  
% 7.37/1.49  fof(f18,plain,(
% 7.37/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.37/1.49    inference(flattening,[],[f17])).
% 7.37/1.49  
% 7.37/1.49  fof(f67,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f18])).
% 7.37/1.49  
% 7.37/1.49  fof(f10,axiom,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f29,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f10])).
% 7.37/1.49  
% 7.37/1.49  fof(f30,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f29])).
% 7.37/1.49  
% 7.37/1.49  fof(f84,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f30])).
% 7.37/1.49  
% 7.37/1.49  fof(f11,axiom,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f31,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f11])).
% 7.37/1.49  
% 7.37/1.49  fof(f32,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f31])).
% 7.37/1.49  
% 7.37/1.49  fof(f85,plain,(
% 7.37/1.49    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f32])).
% 7.37/1.49  
% 7.37/1.49  fof(f5,axiom,(
% 7.37/1.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f20,plain,(
% 7.37/1.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.37/1.49    inference(ennf_transformation,[],[f5])).
% 7.37/1.49  
% 7.37/1.49  fof(f69,plain,(
% 7.37/1.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f20])).
% 7.37/1.49  
% 7.37/1.49  fof(f8,axiom,(
% 7.37/1.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f25,plain,(
% 7.37/1.49    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f8])).
% 7.37/1.49  
% 7.37/1.49  fof(f26,plain,(
% 7.37/1.49    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f25])).
% 7.37/1.49  
% 7.37/1.49  fof(f81,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f26])).
% 7.37/1.49  
% 7.37/1.49  fof(f80,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f26])).
% 7.37/1.49  
% 7.37/1.49  fof(f79,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f26])).
% 7.37/1.49  
% 7.37/1.49  fof(f78,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f26])).
% 7.37/1.49  
% 7.37/1.49  fof(f14,axiom,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f37,plain,(
% 7.37/1.49    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f14])).
% 7.37/1.49  
% 7.37/1.49  fof(f38,plain,(
% 7.37/1.49    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f37])).
% 7.37/1.49  
% 7.37/1.49  fof(f53,plain,(
% 7.37/1.49    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(nnf_transformation,[],[f38])).
% 7.37/1.49  
% 7.37/1.49  fof(f54,plain,(
% 7.37/1.49    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(rectify,[],[f53])).
% 7.37/1.49  
% 7.37/1.49  fof(f56,plain,(
% 7.37/1.49    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))))),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f55,plain,(
% 7.37/1.49    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK5(X0),k6_yellow_6(X0)) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0))))),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f57,plain,(
% 7.37/1.49    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK5(X0),k6_yellow_6(X0)) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f54,f56,f55])).
% 7.37/1.49  
% 7.37/1.49  fof(f97,plain,(
% 7.37/1.49    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f57])).
% 7.37/1.49  
% 7.37/1.49  fof(f92,plain,(
% 7.37/1.49    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f57])).
% 7.37/1.49  
% 7.37/1.49  fof(f93,plain,(
% 7.37/1.49    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f57])).
% 7.37/1.49  
% 7.37/1.49  fof(f94,plain,(
% 7.37/1.49    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK5(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f57])).
% 7.37/1.49  
% 7.37/1.49  fof(f95,plain,(
% 7.37/1.49    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK5(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f57])).
% 7.37/1.49  
% 7.37/1.49  fof(f9,axiom,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f27,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f9])).
% 7.37/1.49  
% 7.37/1.49  fof(f28,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f27])).
% 7.37/1.49  
% 7.37/1.49  fof(f48,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(nnf_transformation,[],[f28])).
% 7.37/1.49  
% 7.37/1.49  fof(f82,plain,(
% 7.37/1.49    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f48])).
% 7.37/1.49  
% 7.37/1.49  fof(f102,plain,(
% 7.37/1.49    ( ! [X3] : (v3_yellow_6(sK9(X3),sK7) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK7)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f13,axiom,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f35,plain,(
% 7.37/1.49    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f13])).
% 7.37/1.49  
% 7.37/1.49  fof(f36,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f35])).
% 7.37/1.49  
% 7.37/1.49  fof(f51,plain,(
% 7.37/1.49    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f52,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK4(X0,X1)) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f51])).
% 7.37/1.49  
% 7.37/1.49  fof(f89,plain,(
% 7.37/1.49    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK4(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f52])).
% 7.37/1.49  
% 7.37/1.49  fof(f12,axiom,(
% 7.37/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 7.37/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.49  
% 7.37/1.49  fof(f33,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.37/1.49    inference(ennf_transformation,[],[f12])).
% 7.37/1.49  
% 7.37/1.49  fof(f34,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(flattening,[],[f33])).
% 7.37/1.49  
% 7.37/1.49  fof(f49,plain,(
% 7.37/1.49    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)))),
% 7.37/1.49    introduced(choice_axiom,[])).
% 7.37/1.49  
% 7.37/1.49  fof(f50,plain,(
% 7.37/1.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.37/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f49])).
% 7.37/1.49  
% 7.37/1.49  fof(f86,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (m2_yellow_6(sK3(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f50])).
% 7.37/1.49  
% 7.37/1.49  fof(f83,plain,(
% 7.37/1.49    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f48])).
% 7.37/1.49  
% 7.37/1.49  fof(f107,plain,(
% 7.37/1.49    ( ! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,sK8) | ~v1_compts_1(sK7)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f103,plain,(
% 7.37/1.49    ~v2_struct_0(sK8) | ~v1_compts_1(sK7)),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f104,plain,(
% 7.37/1.49    v4_orders_2(sK8) | ~v1_compts_1(sK7)),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f105,plain,(
% 7.37/1.49    v7_waybel_0(sK8) | ~v1_compts_1(sK7)),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f106,plain,(
% 7.37/1.49    l1_waybel_0(sK8,sK7) | ~v1_compts_1(sK7)),
% 7.37/1.49    inference(cnf_transformation,[],[f64])).
% 7.37/1.49  
% 7.37/1.49  fof(f88,plain,(
% 7.37/1.49    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f52])).
% 7.37/1.49  
% 7.37/1.49  fof(f87,plain,(
% 7.37/1.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.37/1.49    inference(cnf_transformation,[],[f50])).
% 7.37/1.49  
% 7.37/1.49  cnf(c_39,negated_conjecture,
% 7.37/1.49      ( m2_yellow_6(sK9(X0),sK7,X0)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | v1_compts_1(sK7)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11061,negated_conjecture,
% 7.37/1.49      ( m2_yellow_6(sK9(X0_59),sK7,X0_59)
% 7.37/1.49      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | v1_compts_1(sK7)
% 7.37/1.49      | v2_struct_0(X0_59)
% 7.37/1.49      | ~ v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_39]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11824,plain,
% 7.37/1.49      ( m2_yellow_6(sK9(X0_59),sK7,X0_59) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11061]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.49      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.49      | ~ v2_pre_topc(X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X1) ),
% 7.37/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_41,negated_conjecture,
% 7.37/1.49      ( v2_pre_topc(sK7) ),
% 7.37/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2120,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.49      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X1)
% 7.37/1.49      | sK7 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2121,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_2120]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_42,negated_conjecture,
% 7.37/1.49      ( ~ v2_struct_0(sK7) ),
% 7.37/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_40,negated_conjecture,
% 7.37/1.49      ( l1_pre_topc(sK7) ),
% 7.37/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2125,plain,
% 7.37/1.49      ( ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_2121,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2126,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_2125]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_10,plain,
% 7.37/1.49      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 7.37/1.49      | ~ l1_waybel_0(X1,X0)
% 7.37/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f109]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1913,plain,
% 7.37/1.49      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 7.37/1.49      | ~ l1_waybel_0(X1,X0)
% 7.37/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1914,plain,
% 7.37/1.49      ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1913]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1918,plain,
% 7.37/1.49      ( ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1914,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1919,plain,
% 7.37/1.49      ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_1918]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2143,plain,
% 7.37/1.49      ( m1_connsp_2(sK2(sK7,X0,X1),sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0) ),
% 7.37/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_2126,c_1919]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11039,plain,
% 7.37/1.49      ( m1_connsp_2(sK2(sK7,X0_59,X1_59),sK7,X1_59)
% 7.37/1.49      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59))
% 7.37/1.49      | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0_59)
% 7.37/1.49      | ~ v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2143]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11846,plain,
% 7.37/1.49      ( m1_connsp_2(sK2(sK7,X0_59,X1_59),sK7,X1_59) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11039]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_7,plain,
% 7.37/1.49      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 7.37/1.49      | r1_waybel_0(X1,X2,X0)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | r2_hidden(sK0(X1,X2,X3),X3)
% 7.37/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.49      | ~ v2_pre_topc(X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X1)
% 7.37/1.49      | k10_yellow_6(X1,X2) = X3 ),
% 7.37/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2228,plain,
% 7.37/1.49      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 7.37/1.49      | r1_waybel_0(X1,X2,X0)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | r2_hidden(sK0(X1,X2,X3),X3)
% 7.37/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X1)
% 7.37/1.49      | k10_yellow_6(X1,X2) = X3
% 7.37/1.49      | sK7 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2229,plain,
% 7.37/1.49      ( ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
% 7.37/1.49      | r1_waybel_0(sK7,X1,X0)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | r2_hidden(sK0(sK7,X1,X2),X2)
% 7.37/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ l1_pre_topc(sK7)
% 7.37/1.49      | k10_yellow_6(sK7,X1) = X2 ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_2228]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2233,plain,
% 7.37/1.49      ( ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
% 7.37/1.49      | r1_waybel_0(sK7,X1,X0)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | r2_hidden(sK0(sK7,X1,X2),X2)
% 7.37/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | k10_yellow_6(sK7,X1) = X2 ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_2229,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2234,plain,
% 7.37/1.49      ( ~ m1_connsp_2(X0,sK7,sK0(sK7,X1,X2))
% 7.37/1.49      | r1_waybel_0(sK7,X1,X0)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | r2_hidden(sK0(sK7,X1,X2),X2)
% 7.37/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | k10_yellow_6(sK7,X1) = X2 ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_2233]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11035,plain,
% 7.37/1.49      ( ~ m1_connsp_2(X0_60,sK7,sK0(sK7,X0_59,X1_59))
% 7.37/1.49      | r1_waybel_0(sK7,X0_59,X0_60)
% 7.37/1.49      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59)
% 7.37/1.49      | ~ m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0_59)
% 7.37/1.49      | ~ v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X0_59)
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = X1_59 ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2234]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11850,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | m1_connsp_2(X0_60,sK7,sK0(sK7,X0_59,X1_59)) != iProver_top
% 7.37/1.49      | r1_waybel_0(sK7,X0_59,X0_60) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11035]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_14127,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | r1_waybel_0(sK7,X0_59,sK2(sK7,X2_59,sK0(sK7,X0_59,X1_59))) = iProver_top
% 7.37/1.49      | l1_waybel_0(X2_59,sK7) != iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X2_59)) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X2_59) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X2_59) != iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X2_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_11846,c_11850]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_8,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.49      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 7.37/1.49      | ~ v2_pre_topc(X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X1)
% 7.37/1.49      | k10_yellow_6(X1,X0) = X2 ),
% 7.37/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2195,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.37/1.49      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X1)
% 7.37/1.49      | k10_yellow_6(X1,X0) = X2
% 7.37/1.49      | sK7 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2196,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(sK7)
% 7.37/1.49      | k10_yellow_6(sK7,X0) = X1 ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_2195]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2200,plain,
% 7.37/1.49      ( ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | k10_yellow_6(sK7,X0) = X1 ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_2196,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2201,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0,X1),u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | k10_yellow_6(sK7,X0) = X1 ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_2200]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11036,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0_59)
% 7.37/1.49      | ~ v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X0_59)
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = X1_59 ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2201]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11166,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7)) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11036]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_15380,plain,
% 7.37/1.49      ( m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X2_59)) = iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | l1_waybel_0(X2_59,sK7) != iProver_top
% 7.37/1.49      | r1_waybel_0(sK7,X0_59,sK2(sK7,X2_59,sK0(sK7,X0_59,X1_59))) = iProver_top
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | v2_struct_0(X2_59) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X2_59) != iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X2_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_14127,c_11166]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_15381,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | r1_waybel_0(sK7,X0_59,sK2(sK7,X2_59,sK0(sK7,X0_59,X1_59))) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | l1_waybel_0(X2_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X2_59)) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v2_struct_0(X2_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v4_orders_2(X2_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X2_59) != iProver_top ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_15380]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_9,plain,
% 7.37/1.49      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 7.37/1.49      | ~ l1_waybel_0(X1,X0)
% 7.37/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1949,plain,
% 7.37/1.49      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 7.37/1.49      | ~ l1_waybel_0(X1,X0)
% 7.37/1.49      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1950,plain,
% 7.37/1.49      ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1949]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1954,plain,
% 7.37/1.49      ( ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1950,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1955,plain,
% 7.37/1.49      ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_1954]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2144,plain,
% 7.37/1.49      ( ~ r1_waybel_0(sK7,X0,sK2(sK7,X0,X1))
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0) ),
% 7.37/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_2126,c_1955]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11038,plain,
% 7.37/1.49      ( ~ r1_waybel_0(sK7,X0_59,sK2(sK7,X0_59,X1_59))
% 7.37/1.49      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59))
% 7.37/1.49      | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0_59)
% 7.37/1.49      | ~ v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2144]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11847,plain,
% 7.37/1.49      ( r1_waybel_0(sK7,X0_59,sK2(sK7,X0_59,X1_59)) != iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11038]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_15403,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,X1_59),u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_15381,c_11847]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_20983,plain,
% 7.37/1.49      ( m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_15403,c_11166]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_20984,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = X1_59
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),X1_59) = iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,X1_59),k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_20983]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_0,plain,
% 7.37/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_3,plain,
% 7.37/1.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_475,plain,
% 7.37/1.49      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_476,plain,
% 7.37/1.49      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_475]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11059,plain,
% 7.37/1.49      ( ~ r2_hidden(X0_59,k1_xboole_0) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_476]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11826,plain,
% 7.37/1.49      ( r2_hidden(X0_59,k1_xboole_0) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11059]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_21004,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,k1_xboole_0),k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_20984,c_11826]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1,plain,
% 7.37/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.37/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11067,plain,
% 7.37/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_61)) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12509,plain,
% 7.37/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) ),
% 7.37/1.49      inference(instantiation,[status(thm)],[c_11067]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12512,plain,
% 7.37/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_12509]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_21142,plain,
% 7.37/1.49      ( r2_hidden(sK0(sK7,X0_59,k1_xboole_0),k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_21004,c_12512]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_21143,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(sK0(sK7,X0_59,k1_xboole_0),k10_yellow_6(sK7,X0_59)) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_21142]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11040,plain,
% 7.37/1.49      ( ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | m1_subset_1(k10_yellow_6(sK7,X0_59),k1_zfmisc_1(u1_struct_0(sK7)))
% 7.37/1.49      | v2_struct_0(X0_59)
% 7.37/1.49      | ~ v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2126]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11845,plain,
% 7.37/1.49      ( l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | m1_subset_1(k10_yellow_6(sK7,X0_59),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11040]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2,plain,
% 7.37/1.49      ( ~ r2_hidden(X0,X1)
% 7.37/1.49      | m1_subset_1(X0,X2)
% 7.37/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.37/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11066,plain,
% 7.37/1.49      ( ~ r2_hidden(X0_59,X1_59)
% 7.37/1.49      | m1_subset_1(X0_59,X0_61)
% 7.37/1.49      | ~ m1_subset_1(X1_59,k1_zfmisc_1(X0_61)) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11819,plain,
% 7.37/1.49      ( r2_hidden(X0_59,X1_59) != iProver_top
% 7.37/1.49      | m1_subset_1(X0_59,X0_61) = iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,k1_zfmisc_1(X0_61)) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11066]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12656,plain,
% 7.37/1.49      ( l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,u1_struct_0(sK7)) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_11845,c_11819]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_21156,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_21143,c_12656]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_19,plain,
% 7.37/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X1,X0)
% 7.37/1.49      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1880,plain,
% 7.37/1.49      ( r3_waybel_9(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X1,X0)
% 7.37/1.49      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1881,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,X0,X1)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1880]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1885,plain,
% 7.37/1.49      ( ~ v7_waybel_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | r3_waybel_9(sK7,X0,X1)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1881,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1886,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,X0,X1)
% 7.37/1.49      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.49      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X0) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_1885]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11045,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,X0_59,X1_59)
% 7.37/1.49      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | ~ r2_hidden(X1_59,k10_yellow_6(sK7,X0_59))
% 7.37/1.49      | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X0_59)
% 7.37/1.49      | ~ v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_1886]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11840,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11045]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11151,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11045]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_13731,plain,
% 7.37/1.49      ( r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_11840,c_11151,c_12656]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_13732,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,X0_59,X1_59) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | r2_hidden(X1_59,k10_yellow_6(sK7,X0_59)) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_13731]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_21155,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | r3_waybel_9(sK7,X0_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_21143,c_13732]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_20,plain,
% 7.37/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.37/1.49      | r3_waybel_9(X0,X3,X2)
% 7.37/1.49      | ~ m2_yellow_6(X1,X0,X3)
% 7.37/1.49      | ~ l1_waybel_0(X3,X0)
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X3)
% 7.37/1.49      | ~ v4_orders_2(X3)
% 7.37/1.49      | ~ v7_waybel_0(X3)
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1848,plain,
% 7.37/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.37/1.49      | r3_waybel_9(X0,X3,X2)
% 7.37/1.49      | ~ m2_yellow_6(X1,X0,X3)
% 7.37/1.49      | ~ l1_waybel_0(X3,X0)
% 7.37/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X3)
% 7.37/1.49      | ~ v4_orders_2(X3)
% 7.37/1.49      | ~ v7_waybel_0(X3)
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1849,plain,
% 7.37/1.49      ( ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.49      | r3_waybel_9(sK7,X2,X1)
% 7.37/1.49      | ~ m2_yellow_6(X0,sK7,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1848]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1851,plain,
% 7.37/1.49      ( ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.49      | r3_waybel_9(sK7,X2,X1)
% 7.37/1.49      | ~ m2_yellow_6(X0,sK7,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X2) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1849,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1852,plain,
% 7.37/1.49      ( ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.49      | r3_waybel_9(sK7,X2,X1)
% 7.37/1.49      | ~ m2_yellow_6(X0,sK7,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_1851]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11046,plain,
% 7.37/1.49      ( ~ r3_waybel_9(sK7,X0_59,X1_59)
% 7.37/1.49      | r3_waybel_9(sK7,X2_59,X1_59)
% 7.37/1.49      | ~ m2_yellow_6(X0_59,sK7,X2_59)
% 7.37/1.49      | ~ l1_waybel_0(X2_59,sK7)
% 7.37/1.49      | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
% 7.37/1.49      | v2_struct_0(X2_59)
% 7.37/1.49      | ~ v4_orders_2(X2_59)
% 7.37/1.49      | ~ v7_waybel_0(X2_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_1852]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11839,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
% 7.37/1.49      | r3_waybel_9(sK7,X2_59,X1_59) = iProver_top
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,X2_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X2_59,sK7) != iProver_top
% 7.37/1.49      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X2_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X2_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X2_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11046]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_21399,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | r3_waybel_9(sK7,X1_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_21155,c_11839]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_4,plain,
% 7.37/1.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_13,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | l1_waybel_0(X0,X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_struct_0(X1) ),
% 7.37/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_570,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | l1_waybel_0(X0,X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X3)
% 7.37/1.49      | X1 != X3 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_571,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | l1_waybel_0(X0,X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X1) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_570]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2416,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | l1_waybel_0(X0,X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | sK7 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_571,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2417,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | l1_waybel_0(X0,sK7)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_2416]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2419,plain,
% 7.37/1.49      ( v2_struct_0(X1)
% 7.37/1.49      | l1_waybel_0(X0,sK7)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2417,c_42]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2420,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | l1_waybel_0(X0,sK7)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_2419]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11034,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0_59,sK7,X1_59)
% 7.37/1.49      | ~ l1_waybel_0(X1_59,sK7)
% 7.37/1.49      | l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | v2_struct_0(X1_59)
% 7.37/1.49      | ~ v4_orders_2(X1_59)
% 7.37/1.49      | ~ v7_waybel_0(X1_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2420]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11172,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11034]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_14,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_struct_0(X1) ),
% 7.37/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_542,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X3)
% 7.37/1.49      | X1 != X3 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_543,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | v7_waybel_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X1) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_542]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2442,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | v7_waybel_0(X0)
% 7.37/1.49      | sK7 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_543,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2443,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | v7_waybel_0(X0) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_2442]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2445,plain,
% 7.37/1.49      ( v2_struct_0(X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | v7_waybel_0(X0) ),
% 7.37/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2443,c_42]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2446,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1)
% 7.37/1.49      | v7_waybel_0(X0) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_2445]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11033,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0_59,sK7,X1_59)
% 7.37/1.49      | ~ l1_waybel_0(X1_59,sK7)
% 7.37/1.49      | v2_struct_0(X1_59)
% 7.37/1.49      | ~ v4_orders_2(X1_59)
% 7.37/1.49      | ~ v7_waybel_0(X1_59)
% 7.37/1.49      | v7_waybel_0(X0_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2446]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11173,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) = iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11033]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_15,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_struct_0(X1) ),
% 7.37/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_514,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X3)
% 7.37/1.49      | X1 != X3 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_515,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X1) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_514]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2468,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | sK7 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_515,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2469,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_2468]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2471,plain,
% 7.37/1.49      ( v2_struct_0(X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2469,c_42]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2472,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | v4_orders_2(X0)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_2471]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11032,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0_59,sK7,X1_59)
% 7.37/1.49      | ~ l1_waybel_0(X1_59,sK7)
% 7.37/1.49      | v2_struct_0(X1_59)
% 7.37/1.49      | ~ v4_orders_2(X1_59)
% 7.37/1.49      | v4_orders_2(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(X1_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2472]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11174,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) = iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11032]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_16,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | ~ v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_struct_0(X1) ),
% 7.37/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_486,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | ~ v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X3)
% 7.37/1.49      | X1 != X3 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_487,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | ~ v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | ~ l1_pre_topc(X1) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_486]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2494,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.37/1.49      | ~ l1_waybel_0(X2,X1)
% 7.37/1.49      | ~ v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X2)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X2)
% 7.37/1.49      | ~ v7_waybel_0(X2)
% 7.37/1.49      | sK7 != X1 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_487,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2495,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | ~ v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_2494]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2497,plain,
% 7.37/1.49      ( v2_struct_0(X1)
% 7.37/1.49      | ~ v2_struct_0(X0)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2495,c_42]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_2498,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0,sK7,X1)
% 7.37/1.49      | ~ l1_waybel_0(X1,sK7)
% 7.37/1.49      | ~ v2_struct_0(X0)
% 7.37/1.49      | v2_struct_0(X1)
% 7.37/1.49      | ~ v4_orders_2(X1)
% 7.37/1.49      | ~ v7_waybel_0(X1) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_2497]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11031,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0_59,sK7,X1_59)
% 7.37/1.49      | ~ l1_waybel_0(X1_59,sK7)
% 7.37/1.49      | ~ v2_struct_0(X0_59)
% 7.37/1.49      | v2_struct_0(X1_59)
% 7.37/1.49      | ~ v4_orders_2(X1_59)
% 7.37/1.49      | ~ v7_waybel_0(X1_59) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_2498]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11175,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) != iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11031]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_22691,plain,
% 7.37/1.49      ( v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | r3_waybel_9(sK7,X1_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_21399,c_11172,c_11173,c_11174,c_11175,c_21156]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_22692,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | r3_waybel_9(sK7,X1_59,sK0(sK7,X0_59,k1_xboole_0)) = iProver_top
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_22691]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_25,plain,
% 7.37/1.49      ( ~ r3_waybel_9(X0,sK5(X0),X1)
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.37/1.49      | v1_compts_1(X0)
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1731,plain,
% 7.37/1.49      ( ~ r3_waybel_9(X0,sK5(X0),X1)
% 7.37/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.37/1.49      | v1_compts_1(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1732,plain,
% 7.37/1.49      ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
% 7.37/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 7.37/1.49      | v1_compts_1(sK7)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1731]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1736,plain,
% 7.37/1.49      ( ~ r3_waybel_9(sK7,sK5(sK7),X0)
% 7.37/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 7.37/1.49      | v1_compts_1(sK7) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1732,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11050,plain,
% 7.37/1.49      ( ~ r3_waybel_9(sK7,sK5(sK7),X0_59)
% 7.37/1.49      | ~ m1_subset_1(X0_59,u1_struct_0(sK7))
% 7.37/1.49      | v1_compts_1(sK7) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_1736]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11835,plain,
% 7.37/1.49      ( r3_waybel_9(sK7,sK5(sK7),X0_59) != iProver_top
% 7.37/1.49      | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11050]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_22705,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(sK5(sK7)) = iProver_top
% 7.37/1.49      | v4_orders_2(sK5(sK7)) != iProver_top
% 7.37/1.49      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_22692,c_11835]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_30,plain,
% 7.37/1.49      ( v1_compts_1(X0)
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v2_struct_0(sK5(X0))
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1661,plain,
% 7.37/1.49      ( v1_compts_1(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ v2_struct_0(sK5(X0))
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1662,plain,
% 7.37/1.49      ( v1_compts_1(sK7)
% 7.37/1.49      | ~ v2_struct_0(sK5(sK7))
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1661]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1664,plain,
% 7.37/1.49      ( v1_compts_1(sK7) | ~ v2_struct_0(sK5(sK7)) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1662,c_42,c_41,c_40,c_66]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1666,plain,
% 7.37/1.49      ( v1_compts_1(sK7) = iProver_top | v2_struct_0(sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_1664]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_29,plain,
% 7.37/1.49      ( v1_compts_1(X0)
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v4_orders_2(sK5(X0))
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1675,plain,
% 7.37/1.49      ( v1_compts_1(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v4_orders_2(sK5(X0))
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1676,plain,
% 7.37/1.49      ( v1_compts_1(sK7)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | v4_orders_2(sK5(sK7))
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1675]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1678,plain,
% 7.37/1.49      ( v4_orders_2(sK5(sK7)) | v1_compts_1(sK7) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1676,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1679,plain,
% 7.37/1.49      ( v1_compts_1(sK7) | v4_orders_2(sK5(sK7)) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_1678]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1680,plain,
% 7.37/1.49      ( v1_compts_1(sK7) = iProver_top | v4_orders_2(sK5(sK7)) = iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_1679]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_28,plain,
% 7.37/1.49      ( v1_compts_1(X0)
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v7_waybel_0(sK5(X0))
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1689,plain,
% 7.37/1.49      ( v1_compts_1(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | v7_waybel_0(sK5(X0))
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_28,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1690,plain,
% 7.37/1.49      ( v1_compts_1(sK7)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | v7_waybel_0(sK5(sK7))
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1689]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1692,plain,
% 7.37/1.49      ( v7_waybel_0(sK5(sK7)) | v1_compts_1(sK7) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1690,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1693,plain,
% 7.37/1.49      ( v1_compts_1(sK7) | v7_waybel_0(sK5(sK7)) ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_1692]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1694,plain,
% 7.37/1.49      ( v1_compts_1(sK7) = iProver_top | v7_waybel_0(sK5(sK7)) = iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_27,plain,
% 7.37/1.49      ( l1_waybel_0(sK5(X0),X0)
% 7.37/1.49      | v1_compts_1(X0)
% 7.37/1.49      | ~ v2_pre_topc(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X0) ),
% 7.37/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1703,plain,
% 7.37/1.49      ( l1_waybel_0(sK5(X0),X0)
% 7.37/1.49      | v1_compts_1(X0)
% 7.37/1.49      | v2_struct_0(X0)
% 7.37/1.49      | ~ l1_pre_topc(X0)
% 7.37/1.49      | sK7 != X0 ),
% 7.37/1.49      inference(resolution_lifted,[status(thm)],[c_27,c_41]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1704,plain,
% 7.37/1.49      ( l1_waybel_0(sK5(sK7),sK7)
% 7.37/1.49      | v1_compts_1(sK7)
% 7.37/1.49      | v2_struct_0(sK7)
% 7.37/1.49      | ~ l1_pre_topc(sK7) ),
% 7.37/1.49      inference(unflattening,[status(thm)],[c_1703]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1706,plain,
% 7.37/1.49      ( l1_waybel_0(sK5(sK7),sK7) | v1_compts_1(sK7) ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_1704,c_42,c_40]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_1708,plain,
% 7.37/1.49      ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_1706]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_22807,plain,
% 7.37/1.49      ( v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_22705,c_1666,c_1680,c_1694,c_1708]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_22808,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | m1_subset_1(sK0(sK7,X0_59,k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_22807]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_22818,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_21156,c_22808]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12554,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0_59,sK7,sK5(sK7))
% 7.37/1.49      | ~ l1_waybel_0(sK5(sK7),sK7)
% 7.37/1.49      | v2_struct_0(sK5(sK7))
% 7.37/1.49      | v4_orders_2(X0_59)
% 7.37/1.49      | ~ v4_orders_2(sK5(sK7))
% 7.37/1.49      | ~ v7_waybel_0(sK5(sK7)) ),
% 7.37/1.49      inference(instantiation,[status(thm)],[c_11032]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12555,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(sK5(sK7)) = iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) = iProver_top
% 7.37/1.49      | v4_orders_2(sK5(sK7)) != iProver_top
% 7.37/1.49      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_12554]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12553,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0_59,sK7,sK5(sK7))
% 7.37/1.49      | ~ l1_waybel_0(sK5(sK7),sK7)
% 7.37/1.49      | v2_struct_0(sK5(sK7))
% 7.37/1.49      | ~ v4_orders_2(sK5(sK7))
% 7.37/1.49      | v7_waybel_0(X0_59)
% 7.37/1.49      | ~ v7_waybel_0(sK5(sK7)) ),
% 7.37/1.49      inference(instantiation,[status(thm)],[c_11033]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12559,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(sK5(sK7)) = iProver_top
% 7.37/1.49      | v4_orders_2(sK5(sK7)) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) = iProver_top
% 7.37/1.49      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_12553]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12552,plain,
% 7.37/1.49      ( ~ m2_yellow_6(X0_59,sK7,sK5(sK7))
% 7.37/1.49      | l1_waybel_0(X0_59,sK7)
% 7.37/1.49      | ~ l1_waybel_0(sK5(sK7),sK7)
% 7.37/1.49      | v2_struct_0(sK5(sK7))
% 7.37/1.49      | ~ v4_orders_2(sK5(sK7))
% 7.37/1.49      | ~ v7_waybel_0(sK5(sK7)) ),
% 7.37/1.49      inference(instantiation,[status(thm)],[c_11034]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12563,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | l1_waybel_0(X0_59,sK7) = iProver_top
% 7.37/1.49      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(sK5(sK7)) = iProver_top
% 7.37/1.49      | v4_orders_2(sK5(sK7)) != iProver_top
% 7.37/1.49      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_12552]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_23805,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top ),
% 7.37/1.49      inference(global_propositional_subsumption,
% 7.37/1.49                [status(thm)],
% 7.37/1.49                [c_22818,c_1666,c_1680,c_1694,c_1708,c_12555,c_12559,c_12563,
% 7.37/1.49                 c_21156,c_22808]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_23806,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.49      | m2_yellow_6(X0_59,sK7,sK5(sK7)) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top ),
% 7.37/1.49      inference(renaming,[status(thm)],[c_23805]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_23816,plain,
% 7.37/1.49      ( k10_yellow_6(sK7,sK9(sK5(sK7))) = k1_xboole_0
% 7.37/1.49      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(sK9(sK5(sK7))) = iProver_top
% 7.37/1.49      | v2_struct_0(sK5(sK7)) = iProver_top
% 7.37/1.49      | v4_orders_2(sK5(sK7)) != iProver_top
% 7.37/1.49      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_11824,c_23806]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11052,plain,
% 7.37/1.49      ( l1_waybel_0(sK5(sK7),sK7) | v1_compts_1(sK7) ),
% 7.37/1.49      inference(subtyping,[status(esa)],[c_1706]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11833,plain,
% 7.37/1.49      ( l1_waybel_0(sK5(sK7),sK7) = iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11052]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_11854,plain,
% 7.37/1.49      ( m2_yellow_6(X0_59,sK7,X1_59) != iProver_top
% 7.37/1.49      | l1_waybel_0(X1_59,sK7) != iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) != iProver_top
% 7.37/1.49      | v2_struct_0(X1_59) = iProver_top
% 7.37/1.49      | v4_orders_2(X1_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X1_59) != iProver_top ),
% 7.37/1.49      inference(predicate_to_equality,[status(thm)],[c_11031]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12498,plain,
% 7.37/1.49      ( l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.49      | v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.49      | v2_struct_0(sK9(X0_59)) != iProver_top
% 7.37/1.49      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.49      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_11824,c_11854]) ).
% 7.37/1.49  
% 7.37/1.49  cnf(c_12743,plain,
% 7.37/1.49      ( v1_compts_1(sK7) = iProver_top
% 7.37/1.49      | v2_struct_0(sK9(sK5(sK7))) != iProver_top
% 7.37/1.49      | v2_struct_0(sK5(sK7)) = iProver_top
% 7.37/1.49      | v4_orders_2(sK5(sK7)) != iProver_top
% 7.37/1.49      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 7.37/1.49      inference(superposition,[status(thm)],[c_11833,c_12498]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12908,plain,
% 7.37/1.50      ( v2_struct_0(sK9(sK5(sK7))) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) = iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_12743,c_1666,c_1680,c_1694]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12909,plain,
% 7.37/1.50      ( v1_compts_1(sK7) = iProver_top
% 7.37/1.50      | v2_struct_0(sK9(sK5(sK7))) != iProver_top ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_12908]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1388,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X2,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | ~ v2_struct_0(X3)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X2)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(X2)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v7_waybel_0(X2)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | X2 != X0
% 7.37/1.50      | sK9(X2) != X3
% 7.37/1.50      | sK7 != X1 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_487,c_39]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1389,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v2_struct_0(sK9(X0))
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_1388]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1393,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v2_struct_0(sK9(X0)) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1389,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1394,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v2_struct_0(sK9(X0))
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_1393]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1358,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X2,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X2)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(X2)
% 7.37/1.50      | v4_orders_2(X3)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v7_waybel_0(X2)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | X2 != X0
% 7.37/1.50      | sK9(X2) != X3
% 7.37/1.50      | sK7 != X1 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_515,c_39]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1359,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_1358]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1363,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1359,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1364,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_1363]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1328,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X2,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X2)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(X2)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v7_waybel_0(X2)
% 7.37/1.50      | v7_waybel_0(X3)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | X2 != X0
% 7.37/1.50      | sK9(X2) != X3
% 7.37/1.50      | sK7 != X1 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_543,c_39]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1329,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | v7_waybel_0(sK9(X0))
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_1328]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1333,plain,
% 7.37/1.50      ( v7_waybel_0(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1329,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1334,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | v7_waybel_0(sK9(X0)) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_1333]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1298,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | l1_waybel_0(X2,X1)
% 7.37/1.50      | ~ l1_waybel_0(X3,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X3)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(X3)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v7_waybel_0(X3)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | X3 != X0
% 7.37/1.50      | sK9(X3) != X2
% 7.37/1.50      | sK7 != X1 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_571,c_39]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1299,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | l1_waybel_0(sK9(X0),sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_1298]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1303,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | l1_waybel_0(sK9(X0),sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1299,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1304,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | l1_waybel_0(sK9(X0),sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_1303]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_18,plain,
% 7.37/1.50      ( ~ v3_yellow_6(X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | ~ v2_pre_topc(X1)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 7.37/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_38,negated_conjecture,
% 7.37/1.50      ( v3_yellow_6(sK9(X0),sK7)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_668,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X2,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | ~ v2_pre_topc(X1)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X2)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X2)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X2)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | k10_yellow_6(X1,X0) != k1_xboole_0
% 7.37/1.50      | sK9(X2) != X0
% 7.37/1.50      | sK7 != X1 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_18,c_38]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_669,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ l1_waybel_0(sK9(X0),sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | ~ v2_pre_topc(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK9(X0))
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v7_waybel_0(sK9(X0))
% 7.37/1.50      | ~ l1_pre_topc(sK7)
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_668]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_673,plain,
% 7.37/1.50      ( ~ v7_waybel_0(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | ~ l1_waybel_0(sK9(X0),sK7)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK9(X0))
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_669,c_42,c_41,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_674,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ l1_waybel_0(sK9(X0),sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK9(X0))
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v7_waybel_0(sK9(X0))
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_673]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1574,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK9(X0))
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v7_waybel_0(sK9(X0))
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 7.37/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_1304,c_674]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1588,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK9(X0))
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v4_orders_2(sK9(X0))
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 7.37/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_1334,c_1574]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1597,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK9(X0))
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 7.37/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_1364,c_1588]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1606,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 7.37/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_1394,c_1597]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11057,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0_59)
% 7.37/1.50      | ~ v4_orders_2(X0_59)
% 7.37/1.50      | ~ v7_waybel_0(X0_59)
% 7.37/1.50      | k10_yellow_6(sK7,sK9(X0_59)) != k1_xboole_0 ),
% 7.37/1.50      inference(subtyping,[status(esa)],[c_1606]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12945,plain,
% 7.37/1.50      ( ~ l1_waybel_0(sK5(sK7),sK7)
% 7.37/1.50      | v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(sK5(sK7))
% 7.37/1.50      | ~ v4_orders_2(sK5(sK7))
% 7.37/1.50      | ~ v7_waybel_0(sK5(sK7))
% 7.37/1.50      | k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0 ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_11057]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12946,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,sK9(sK5(sK7))) != k1_xboole_0
% 7.37/1.50      | l1_waybel_0(sK5(sK7),sK7) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) = iProver_top
% 7.37/1.50      | v2_struct_0(sK5(sK7)) = iProver_top
% 7.37/1.50      | v4_orders_2(sK5(sK7)) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK5(sK7)) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_12945]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_23842,plain,
% 7.37/1.50      ( v1_compts_1(sK7) = iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_23816,c_1666,c_1680,c_1694,c_1708,c_12909,c_12946]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_23,plain,
% 7.37/1.50      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 7.37/1.50      | ~ l1_waybel_0(X1,X0)
% 7.37/1.50      | ~ v1_compts_1(X0)
% 7.37/1.50      | ~ v2_pre_topc(X0)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X1)
% 7.37/1.50      | ~ v7_waybel_0(X1)
% 7.37/1.50      | ~ l1_pre_topc(X0) ),
% 7.37/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1752,plain,
% 7.37/1.50      ( r3_waybel_9(X0,X1,sK4(X0,X1))
% 7.37/1.50      | ~ l1_waybel_0(X1,X0)
% 7.37/1.50      | ~ v1_compts_1(X0)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X1)
% 7.37/1.50      | ~ v7_waybel_0(X1)
% 7.37/1.50      | ~ l1_pre_topc(X0)
% 7.37/1.50      | sK7 != X0 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_23,c_41]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1753,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_1752]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1757,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1753,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1758,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,X0,sK4(sK7,X0))
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_1757]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11049,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,X0_59,sK4(sK7,X0_59))
% 7.37/1.50      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0_59)
% 7.37/1.50      | ~ v4_orders_2(X0_59)
% 7.37/1.50      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.50      inference(subtyping,[status(esa)],[c_1758]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11836,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,X0_59,sK4(sK7,X0_59)) = iProver_top
% 7.37/1.50      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.50      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.50      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_11049]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22,plain,
% 7.37/1.50      ( ~ r3_waybel_9(X0,X1,X2)
% 7.37/1.50      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X1,X0)
% 7.37/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.50      | ~ v2_pre_topc(X0)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X1)
% 7.37/1.50      | ~ v7_waybel_0(X1)
% 7.37/1.50      | ~ l1_pre_topc(X0) ),
% 7.37/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1782,plain,
% 7.37/1.50      ( ~ r3_waybel_9(X0,X1,X2)
% 7.37/1.50      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X1,X0)
% 7.37/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X1)
% 7.37/1.50      | ~ v7_waybel_0(X1)
% 7.37/1.50      | ~ l1_pre_topc(X0)
% 7.37/1.50      | sK7 != X0 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_41]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1783,plain,
% 7.37/1.50      ( ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.50      | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_1782]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1787,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.50      | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1783,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1788,plain,
% 7.37/1.50      ( ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.50      | m2_yellow_6(sK3(sK7,X0,X1),sK7,X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_1787]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11048,plain,
% 7.37/1.50      ( ~ r3_waybel_9(sK7,X0_59,X1_59)
% 7.37/1.50      | m2_yellow_6(sK3(sK7,X0_59,X1_59),sK7,X0_59)
% 7.37/1.50      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.50      | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0_59)
% 7.37/1.50      | ~ v4_orders_2(X0_59)
% 7.37/1.50      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.50      inference(subtyping,[status(esa)],[c_1788]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11837,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
% 7.37/1.50      | m2_yellow_6(sK3(sK7,X0_59,X1_59),sK7,X0_59) = iProver_top
% 7.37/1.50      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.50      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.50      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.50      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_11048]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_13386,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
% 7.37/1.50      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.50      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.50      | v2_struct_0(sK3(sK7,X0_59,X1_59)) != iProver_top
% 7.37/1.50      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.50      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_11837,c_11854]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_17,plain,
% 7.37/1.50      ( v3_yellow_6(X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | ~ v2_pre_topc(X1)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 7.37/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_33,negated_conjecture,
% 7.37/1.50      ( ~ m2_yellow_6(X0,sK7,sK8)
% 7.37/1.50      | ~ v3_yellow_6(X0,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7) ),
% 7.37/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_635,plain,
% 7.37/1.50      ( ~ m2_yellow_6(X0,sK7,sK8)
% 7.37/1.50      | ~ l1_waybel_0(X1,X2)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | ~ v2_pre_topc(X2)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X2)
% 7.37/1.50      | ~ v4_orders_2(X1)
% 7.37/1.50      | ~ v7_waybel_0(X1)
% 7.37/1.50      | ~ l1_pre_topc(X2)
% 7.37/1.50      | X0 != X1
% 7.37/1.50      | k10_yellow_6(X2,X1) = k1_xboole_0
% 7.37/1.50      | sK7 != X2 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_636,plain,
% 7.37/1.50      ( ~ m2_yellow_6(X0,sK7,sK8)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | ~ v2_pre_topc(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7)
% 7.37/1.50      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_635]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_640,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ m2_yellow_6(X0,sK7,sK8)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_636,c_42,c_41,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_641,plain,
% 7.37/1.50      ( ~ m2_yellow_6(X0,sK7,sK8)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_640]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11058,plain,
% 7.37/1.50      ( ~ m2_yellow_6(X0_59,sK7,sK8)
% 7.37/1.50      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0_59)
% 7.37/1.50      | ~ v4_orders_2(X0_59)
% 7.37/1.50      | ~ v7_waybel_0(X0_59)
% 7.37/1.50      | k10_yellow_6(sK7,X0_59) = k1_xboole_0 ),
% 7.37/1.50      inference(subtyping,[status(esa)],[c_641]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11827,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.50      | m2_yellow_6(X0_59,sK7,sK8) != iProver_top
% 7.37/1.50      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.50      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.50      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_11058]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_37,negated_conjecture,
% 7.37/1.50      ( ~ v1_compts_1(sK7) | ~ v2_struct_0(sK8) ),
% 7.37/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_52,plain,
% 7.37/1.50      ( v1_compts_1(sK7) != iProver_top | v2_struct_0(sK8) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_36,negated_conjecture,
% 7.37/1.50      ( ~ v1_compts_1(sK7) | v4_orders_2(sK8) ),
% 7.37/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_53,plain,
% 7.37/1.50      ( v1_compts_1(sK7) != iProver_top | v4_orders_2(sK8) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_35,negated_conjecture,
% 7.37/1.50      ( ~ v1_compts_1(sK7) | v7_waybel_0(sK8) ),
% 7.37/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_54,plain,
% 7.37/1.50      ( v1_compts_1(sK7) != iProver_top | v7_waybel_0(sK8) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_34,negated_conjecture,
% 7.37/1.50      ( l1_waybel_0(sK8,sK7) | ~ v1_compts_1(sK7) ),
% 7.37/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_55,plain,
% 7.37/1.50      ( l1_waybel_0(sK8,sK7) = iProver_top | v1_compts_1(sK7) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11134,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.50      | m2_yellow_6(X0_59,sK7,sK8) != iProver_top
% 7.37/1.50      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.50      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.50      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_11058]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12328,plain,
% 7.37/1.50      ( ~ m2_yellow_6(X0_59,sK7,sK8)
% 7.37/1.50      | ~ l1_waybel_0(sK8,sK7)
% 7.37/1.50      | v2_struct_0(sK8)
% 7.37/1.50      | v4_orders_2(X0_59)
% 7.37/1.50      | ~ v4_orders_2(sK8)
% 7.37/1.50      | ~ v7_waybel_0(sK8) ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_11032]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12329,plain,
% 7.37/1.50      ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(X0_59) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_12328]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12333,plain,
% 7.37/1.50      ( ~ m2_yellow_6(X0_59,sK7,sK8)
% 7.37/1.50      | ~ l1_waybel_0(sK8,sK7)
% 7.37/1.50      | v2_struct_0(sK8)
% 7.37/1.50      | ~ v4_orders_2(sK8)
% 7.37/1.50      | v7_waybel_0(X0_59)
% 7.37/1.50      | ~ v7_waybel_0(sK8) ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_11033]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12334,plain,
% 7.37/1.50      ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(X0_59) = iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_12333]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12344,plain,
% 7.37/1.50      ( ~ m2_yellow_6(X0_59,sK7,sK8)
% 7.37/1.50      | l1_waybel_0(X0_59,sK7)
% 7.37/1.50      | ~ l1_waybel_0(sK8,sK7)
% 7.37/1.50      | v2_struct_0(sK8)
% 7.37/1.50      | ~ v4_orders_2(sK8)
% 7.37/1.50      | ~ v7_waybel_0(sK8) ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_11034]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12345,plain,
% 7.37/1.50      ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
% 7.37/1.50      | l1_waybel_0(X0_59,sK7) = iProver_top
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_12344]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12440,plain,
% 7.37/1.50      ( m2_yellow_6(X0_59,sK7,sK8) != iProver_top
% 7.37/1.50      | k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_11827,c_52,c_53,c_54,c_55,c_11134,c_12329,c_12334,c_12345]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12441,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,X0_59) = k1_xboole_0
% 7.37/1.50      | m2_yellow_6(X0_59,sK7,sK8) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_12440]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_13387,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
% 7.37/1.50      | r3_waybel_9(sK7,sK8,X0_59) != iProver_top
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK3(sK7,sK8,X0_59)) = iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_11837,c_12441]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_13418,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
% 7.37/1.50      | r3_waybel_9(sK7,sK8,X0_59) != iProver_top
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(backward_subsumption_resolution,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_13386,c_13387]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_14719,plain,
% 7.37/1.50      ( v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
% 7.37/1.50      | r3_waybel_9(sK7,sK8,X0_59) != iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_13418,c_52,c_53,c_54,c_55]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_14720,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,sK3(sK7,sK8,X0_59)) = k1_xboole_0
% 7.37/1.50      | r3_waybel_9(sK7,sK8,X0_59) != iProver_top
% 7.37/1.50      | m1_subset_1(X0_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_14719]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_14729,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_11836,c_14720]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_24,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 7.37/1.50      | ~ v1_compts_1(X1)
% 7.37/1.50      | ~ v2_pre_topc(X1)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(X1) ),
% 7.37/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2090,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,X1)
% 7.37/1.50      | m1_subset_1(sK4(X1,X0),u1_struct_0(X1))
% 7.37/1.50      | ~ v1_compts_1(X1)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(X1)
% 7.37/1.50      | sK7 != X1 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_24,c_41]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2091,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_2090]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2095,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_2091,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2096,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | m1_subset_1(sK4(sK7,X0),u1_struct_0(sK7))
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_2095]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11041,plain,
% 7.37/1.50      ( ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.50      | m1_subset_1(sK4(sK7,X0_59),u1_struct_0(sK7))
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(X0_59)
% 7.37/1.50      | ~ v4_orders_2(X0_59)
% 7.37/1.50      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.50      inference(subtyping,[status(esa)],[c_2096]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12316,plain,
% 7.37/1.50      ( ~ l1_waybel_0(sK8,sK7)
% 7.37/1.50      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7))
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(sK8)
% 7.37/1.50      | ~ v4_orders_2(sK8)
% 7.37/1.50      | ~ v7_waybel_0(sK8) ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_11041]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12317,plain,
% 7.37/1.50      ( l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_12316]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_14907,plain,
% 7.37/1.50      ( v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_14729,c_52,c_53,c_54,c_55,c_12317]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_14908,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_14907]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_23847,plain,
% 7.37/1.50      ( k10_yellow_6(sK7,sK3(sK7,sK8,sK4(sK7,sK8))) = k1_xboole_0 ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_23842,c_14908]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_21,plain,
% 7.37/1.50      ( ~ r3_waybel_9(X0,X1,X2)
% 7.37/1.50      | ~ l1_waybel_0(X1,X0)
% 7.37/1.50      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 7.37/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.50      | ~ v2_pre_topc(X0)
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X1)
% 7.37/1.50      | ~ v7_waybel_0(X1)
% 7.37/1.50      | ~ l1_pre_topc(X0) ),
% 7.37/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1815,plain,
% 7.37/1.50      ( ~ r3_waybel_9(X0,X1,X2)
% 7.37/1.50      | ~ l1_waybel_0(X1,X0)
% 7.37/1.50      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 7.37/1.50      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(X1)
% 7.37/1.50      | ~ v4_orders_2(X1)
% 7.37/1.50      | ~ v7_waybel_0(X1)
% 7.37/1.50      | ~ l1_pre_topc(X0)
% 7.37/1.50      | sK7 != X0 ),
% 7.37/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_41]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1816,plain,
% 7.37/1.50      ( ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
% 7.37/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | v2_struct_0(sK7)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ l1_pre_topc(sK7) ),
% 7.37/1.50      inference(unflattening,[status(thm)],[c_1815]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1820,plain,
% 7.37/1.50      ( ~ v7_waybel_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
% 7.37/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0) ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1816,c_42,c_40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1821,plain,
% 7.37/1.50      ( ~ r3_waybel_9(sK7,X0,X1)
% 7.37/1.50      | ~ l1_waybel_0(X0,sK7)
% 7.37/1.50      | r2_hidden(X1,k10_yellow_6(sK7,sK3(sK7,X0,X1)))
% 7.37/1.50      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0)
% 7.37/1.50      | ~ v4_orders_2(X0)
% 7.37/1.50      | ~ v7_waybel_0(X0) ),
% 7.37/1.50      inference(renaming,[status(thm)],[c_1820]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11047,plain,
% 7.37/1.50      ( ~ r3_waybel_9(sK7,X0_59,X1_59)
% 7.37/1.50      | ~ l1_waybel_0(X0_59,sK7)
% 7.37/1.50      | r2_hidden(X1_59,k10_yellow_6(sK7,sK3(sK7,X0_59,X1_59)))
% 7.37/1.50      | ~ m1_subset_1(X1_59,u1_struct_0(sK7))
% 7.37/1.50      | v2_struct_0(X0_59)
% 7.37/1.50      | ~ v4_orders_2(X0_59)
% 7.37/1.50      | ~ v7_waybel_0(X0_59) ),
% 7.37/1.50      inference(subtyping,[status(esa)],[c_1821]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11838,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,X0_59,X1_59) != iProver_top
% 7.37/1.50      | l1_waybel_0(X0_59,sK7) != iProver_top
% 7.37/1.50      | r2_hidden(X1_59,k10_yellow_6(sK7,sK3(sK7,X0_59,X1_59))) = iProver_top
% 7.37/1.50      | m1_subset_1(X1_59,u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v2_struct_0(X0_59) = iProver_top
% 7.37/1.50      | v4_orders_2(X0_59) != iProver_top
% 7.37/1.50      | v7_waybel_0(X0_59) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_11047]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_24032,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) != iProver_top
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top
% 7.37/1.50      | m1_subset_1(sK4(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_23847,c_11838]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12322,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8))
% 7.37/1.50      | ~ l1_waybel_0(sK8,sK7)
% 7.37/1.50      | ~ v1_compts_1(sK7)
% 7.37/1.50      | v2_struct_0(sK8)
% 7.37/1.50      | ~ v4_orders_2(sK8)
% 7.37/1.50      | ~ v7_waybel_0(sK8) ),
% 7.37/1.50      inference(instantiation,[status(thm)],[c_11049]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12323,plain,
% 7.37/1.50      ( r3_waybel_9(sK7,sK8,sK4(sK7,sK8)) = iProver_top
% 7.37/1.50      | l1_waybel_0(sK8,sK7) != iProver_top
% 7.37/1.50      | v1_compts_1(sK7) != iProver_top
% 7.37/1.50      | v2_struct_0(sK8) = iProver_top
% 7.37/1.50      | v4_orders_2(sK8) != iProver_top
% 7.37/1.50      | v7_waybel_0(sK8) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_12322]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_24428,plain,
% 7.37/1.50      ( r2_hidden(sK4(sK7,sK8),k1_xboole_0) = iProver_top ),
% 7.37/1.50      inference(global_propositional_subsumption,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_24032,c_52,c_53,c_54,c_55,c_1666,c_1680,c_1694,c_1708,
% 7.37/1.50                 c_12317,c_12323,c_12909,c_12946,c_23816]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_24433,plain,
% 7.37/1.50      ( $false ),
% 7.37/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_24428,c_11826]) ).
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.37/1.50  
% 7.37/1.50  ------                               Statistics
% 7.37/1.50  
% 7.37/1.50  ------ General
% 7.37/1.50  
% 7.37/1.50  abstr_ref_over_cycles:                  0
% 7.37/1.50  abstr_ref_under_cycles:                 0
% 7.37/1.50  gc_basic_clause_elim:                   0
% 7.37/1.50  forced_gc_time:                         0
% 7.37/1.50  parsing_time:                           0.013
% 7.37/1.50  unif_index_cands_time:                  0.
% 7.37/1.50  unif_index_add_time:                    0.
% 7.37/1.50  orderings_time:                         0.
% 7.37/1.50  out_proof_time:                         0.023
% 7.37/1.50  total_time:                             0.677
% 7.37/1.50  num_of_symbols:                         65
% 7.37/1.50  num_of_terms:                           10942
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing
% 7.37/1.50  
% 7.37/1.50  num_of_splits:                          0
% 7.37/1.50  num_of_split_atoms:                     0
% 7.37/1.50  num_of_reused_defs:                     0
% 7.37/1.50  num_eq_ax_congr_red:                    51
% 7.37/1.50  num_of_sem_filtered_clauses:            1
% 7.37/1.50  num_of_subtypes:                        3
% 7.37/1.50  monotx_restored_types:                  1
% 7.37/1.50  sat_num_of_epr_types:                   0
% 7.37/1.50  sat_num_of_non_cyclic_types:            0
% 7.37/1.50  sat_guarded_non_collapsed_types:        0
% 7.37/1.50  num_pure_diseq_elim:                    0
% 7.37/1.50  simp_replaced_by:                       0
% 7.37/1.50  res_preprocessed:                       207
% 7.37/1.50  prep_upred:                             0
% 7.37/1.50  prep_unflattend:                        277
% 7.37/1.50  smt_new_axioms:                         0
% 7.37/1.50  pred_elim_cands:                        11
% 7.37/1.50  pred_elim:                              5
% 7.37/1.50  pred_elim_cl:                           6
% 7.37/1.50  pred_elim_cycles:                       18
% 7.37/1.50  merged_defs:                            0
% 7.37/1.50  merged_defs_ncl:                        0
% 7.37/1.50  bin_hyper_res:                          0
% 7.37/1.50  prep_cycles:                            4
% 7.37/1.50  pred_elim_time:                         0.211
% 7.37/1.50  splitting_time:                         0.
% 7.37/1.50  sem_filter_time:                        0.
% 7.37/1.50  monotx_time:                            0.001
% 7.37/1.50  subtype_inf_time:                       0.001
% 7.37/1.50  
% 7.37/1.50  ------ Problem properties
% 7.37/1.50  
% 7.37/1.50  clauses:                                37
% 7.37/1.50  conjectures:                            6
% 7.37/1.50  epr:                                    10
% 7.37/1.50  horn:                                   11
% 7.37/1.50  ground:                                 10
% 7.37/1.50  unary:                                  3
% 7.37/1.50  binary:                                 9
% 7.37/1.50  lits:                                   184
% 7.37/1.50  lits_eq:                                6
% 7.37/1.50  fd_pure:                                0
% 7.37/1.50  fd_pseudo:                              0
% 7.37/1.50  fd_cond:                                0
% 7.37/1.50  fd_pseudo_cond:                         4
% 7.37/1.50  ac_symbols:                             0
% 7.37/1.50  
% 7.37/1.50  ------ Propositional Solver
% 7.37/1.50  
% 7.37/1.50  prop_solver_calls:                      30
% 7.37/1.50  prop_fast_solver_calls:                 7039
% 7.37/1.50  smt_solver_calls:                       0
% 7.37/1.50  smt_fast_solver_calls:                  0
% 7.37/1.50  prop_num_of_clauses:                    4525
% 7.37/1.50  prop_preprocess_simplified:             13615
% 7.37/1.50  prop_fo_subsumed:                       289
% 7.37/1.50  prop_solver_time:                       0.
% 7.37/1.50  smt_solver_time:                        0.
% 7.37/1.50  smt_fast_solver_time:                   0.
% 7.37/1.50  prop_fast_solver_time:                  0.
% 7.37/1.50  prop_unsat_core_time:                   0.
% 7.37/1.50  
% 7.37/1.50  ------ QBF
% 7.37/1.50  
% 7.37/1.50  qbf_q_res:                              0
% 7.37/1.50  qbf_num_tautologies:                    0
% 7.37/1.50  qbf_prep_cycles:                        0
% 7.37/1.50  
% 7.37/1.50  ------ BMC1
% 7.37/1.50  
% 7.37/1.50  bmc1_current_bound:                     -1
% 7.37/1.50  bmc1_last_solved_bound:                 -1
% 7.37/1.50  bmc1_unsat_core_size:                   -1
% 7.37/1.50  bmc1_unsat_core_parents_size:           -1
% 7.37/1.50  bmc1_merge_next_fun:                    0
% 7.37/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.37/1.50  
% 7.37/1.50  ------ Instantiation
% 7.37/1.50  
% 7.37/1.50  inst_num_of_clauses:                    1122
% 7.37/1.50  inst_num_in_passive:                    394
% 7.37/1.50  inst_num_in_active:                     653
% 7.37/1.50  inst_num_in_unprocessed:                75
% 7.37/1.50  inst_num_of_loops:                      770
% 7.37/1.50  inst_num_of_learning_restarts:          0
% 7.37/1.50  inst_num_moves_active_passive:          113
% 7.37/1.50  inst_lit_activity:                      0
% 7.37/1.50  inst_lit_activity_moves:                0
% 7.37/1.50  inst_num_tautologies:                   0
% 7.37/1.50  inst_num_prop_implied:                  0
% 7.37/1.50  inst_num_existing_simplified:           0
% 7.37/1.50  inst_num_eq_res_simplified:             0
% 7.37/1.50  inst_num_child_elim:                    0
% 7.37/1.50  inst_num_of_dismatching_blockings:      100
% 7.37/1.50  inst_num_of_non_proper_insts:           905
% 7.37/1.50  inst_num_of_duplicates:                 0
% 7.37/1.50  inst_inst_num_from_inst_to_res:         0
% 7.37/1.50  inst_dismatching_checking_time:         0.
% 7.37/1.50  
% 7.37/1.50  ------ Resolution
% 7.37/1.50  
% 7.37/1.50  res_num_of_clauses:                     0
% 7.37/1.50  res_num_in_passive:                     0
% 7.37/1.50  res_num_in_active:                      0
% 7.37/1.50  res_num_of_loops:                       211
% 7.37/1.50  res_forward_subset_subsumed:            66
% 7.37/1.50  res_backward_subset_subsumed:           0
% 7.37/1.50  res_forward_subsumed:                   0
% 7.37/1.50  res_backward_subsumed:                  0
% 7.37/1.50  res_forward_subsumption_resolution:     22
% 7.37/1.50  res_backward_subsumption_resolution:    6
% 7.37/1.50  res_clause_to_clause_subsumption:       3326
% 7.37/1.50  res_orphan_elimination:                 0
% 7.37/1.50  res_tautology_del:                      118
% 7.37/1.50  res_num_eq_res_simplified:              0
% 7.37/1.50  res_num_sel_changes:                    0
% 7.37/1.50  res_moves_from_active_to_pass:          0
% 7.37/1.50  
% 7.37/1.50  ------ Superposition
% 7.37/1.50  
% 7.37/1.50  sup_time_total:                         0.
% 7.37/1.50  sup_time_generating:                    0.
% 7.37/1.50  sup_time_sim_full:                      0.
% 7.37/1.50  sup_time_sim_immed:                     0.
% 7.37/1.50  
% 7.37/1.50  sup_num_of_clauses:                     210
% 7.37/1.50  sup_num_in_active:                      144
% 7.37/1.50  sup_num_in_passive:                     66
% 7.37/1.50  sup_num_of_loops:                       152
% 7.37/1.50  sup_fw_superposition:                   81
% 7.37/1.50  sup_bw_superposition:                   215
% 7.37/1.50  sup_immediate_simplified:               68
% 7.37/1.50  sup_given_eliminated:                   0
% 7.37/1.50  comparisons_done:                       0
% 7.37/1.50  comparisons_avoided:                    0
% 7.37/1.50  
% 7.37/1.50  ------ Simplifications
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  sim_fw_subset_subsumed:                 30
% 7.37/1.50  sim_bw_subset_subsumed:                 10
% 7.37/1.50  sim_fw_subsumed:                        35
% 7.37/1.50  sim_bw_subsumed:                        0
% 7.37/1.50  sim_fw_subsumption_res:                 79
% 7.37/1.50  sim_bw_subsumption_res:                 1
% 7.37/1.50  sim_tautology_del:                      36
% 7.37/1.50  sim_eq_tautology_del:                   12
% 7.37/1.50  sim_eq_res_simp:                        1
% 7.37/1.50  sim_fw_demodulated:                     1
% 7.37/1.50  sim_bw_demodulated:                     0
% 7.37/1.50  sim_light_normalised:                   17
% 7.37/1.50  sim_joinable_taut:                      0
% 7.37/1.50  sim_joinable_simp:                      0
% 7.37/1.50  sim_ac_normalised:                      0
% 7.37/1.50  sim_smt_subsumption:                    0
% 7.37/1.50  
%------------------------------------------------------------------------------
