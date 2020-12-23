%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:26 EST 2020

% Result     : Theorem 19.85s
% Output     : CNFRefutation 19.85s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_62)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f67,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK9(X3),X0)
        & m2_yellow_6(sK9(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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

fof(f65,plain,
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

fof(f68,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f64,f67,f66,f65])).

fof(f107,plain,(
    ! [X3] :
      ( m2_yellow_6(sK9(X3),sK7,X3)
      | ~ l1_waybel_0(X3,sK7)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f68])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f24])).

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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f53,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X6))
        & m1_connsp_2(sK3(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
        & m1_connsp_2(sK2(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f53,f52,f51])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f104,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f68])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f85,plain,(
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

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f115,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f54])).

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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f92,plain,(
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

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f93,plain,(
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

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f114,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f60,plain,(
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
            ( ~ r3_waybel_9(X0,sK6(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK6(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK6(X0),X0)
        & v7_waybel_0(sK6(X0))
        & v4_orders_2(sK6(X0))
        & ~ v2_struct_0(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ( ! [X2] :
            ( ~ r3_waybel_9(X0,sK6(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK6(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK6(X0),X0)
        & v7_waybel_0(sK6(X0))
        & v4_orders_2(sK6(X0))
        & ~ v2_struct_0(sK6(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f60])).

fof(f103,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK6(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK6(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK6(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f89,plain,(
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

fof(f88,plain,(
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

fof(f87,plain,(
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

fof(f86,plain,(
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
         => ( v3_yellow_6(X1,X0)
          <=> k1_xboole_0 != k10_yellow_6(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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

fof(f55,plain,(
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

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f108,plain,(
    ! [X3] :
      ( v3_yellow_6(sK9(X3),sK7)
      | ~ l1_waybel_0(X3,sK7)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK5(X0,X1))
            & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f58])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK5(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

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
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
        & m2_yellow_6(sK4(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
                & m2_yellow_6(sK4(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f56])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK4(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK7)
      | ~ m2_yellow_6(X2,sK7,sK8)
      | ~ v1_compts_1(sK7) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f109,plain,
    ( ~ v2_struct_0(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f110,plain,
    ( v4_orders_2(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f111,plain,
    ( v7_waybel_0(sK8)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f112,plain,
    ( l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_41,negated_conjecture,
    ( m2_yellow_6(sK9(X0),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_7863,plain,
    ( m2_yellow_6(sK9(X0),sK7,X0) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_43,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1926,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_43])).

cnf(c_1927,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1926])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_42,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1931,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_44,c_42])).

cnf(c_1932,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1931])).

cnf(c_7842,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_16,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1851,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_43])).

cnf(c_1852,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1851])).

cnf(c_1856,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1852,c_44,c_42])).

cnf(c_1857,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1856])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f115])).

cnf(c_1677,plain,
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
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_43])).

cnf(c_1678,plain,
    ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1677])).

cnf(c_1682,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1678,c_44,c_42])).

cnf(c_1683,plain,
    ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1682])).

cnf(c_1874,plain,
    ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1857,c_1683])).

cnf(c_7845,plain,
    ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1874])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_1959,plain,
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
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_43])).

cnf(c_1960,plain,
    ( ~ m1_connsp_2(X0,sK7,sK1(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK1(sK7,X1,X2),X2)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(sK7)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_1959])).

cnf(c_1964,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_connsp_2(X0,sK7,sK1(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK1(sK7,X1,X2),X2)
    | v2_struct_0(X1)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1960,c_44,c_42])).

cnf(c_1965,plain,
    ( ~ m1_connsp_2(X0,sK7,sK1(sK7,X1,X2))
    | r1_waybel_0(sK7,X1,X0)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK1(sK7,X1,X2),X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | k10_yellow_6(sK7,X1) = X2 ),
    inference(renaming,[status(thm)],[c_1964])).

cnf(c_7841,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | m1_connsp_2(X2,sK7,sK1(sK7,X0,X1)) != iProver_top
    | r1_waybel_0(sK7,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1965])).

cnf(c_10727,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7845,c_7841])).

cnf(c_2472,plain,
    ( r1_waybel_0(sK7,X0,X1)
    | ~ l1_waybel_0(X2,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X3,u1_struct_0(sK7))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(X3,k10_yellow_6(sK7,X2))
    | r2_hidden(sK1(sK7,X0,X4),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X0)
    | sK3(sK7,X2,X3) != X1
    | sK1(sK7,X0,X4) != X3
    | k10_yellow_6(sK7,X0) = X4
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_1874,c_1965])).

cnf(c_2473,plain,
    ( r1_waybel_0(sK7,X0,sK3(sK7,X1,sK1(sK7,X0,X2)))
    | ~ l1_waybel_0(X1,sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(sK1(sK7,X0,X2),u1_struct_0(sK7))
    | r2_hidden(sK1(sK7,X0,X2),X2)
    | r2_hidden(sK1(sK7,X0,X2),k10_yellow_6(sK7,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = X2 ),
    inference(unflattening,[status(thm)],[c_2472])).

cnf(c_2505,plain,
    ( r1_waybel_0(sK7,X0,sK3(sK7,X1,sK1(sK7,X0,X2)))
    | ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK1(sK7,X0,X2),X2)
    | r2_hidden(sK1(sK7,X0,X2),k10_yellow_6(sK7,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2473,c_1932])).

cnf(c_2519,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2505])).

cnf(c_12687,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
    | k10_yellow_6(sK7,X0) = X1
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10727,c_2519])).

cnf(c_12688,plain,
    ( k10_yellow_6(sK7,X0) = X1
    | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
    | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12687])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f92])).

cnf(c_1644,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_43])).

cnf(c_1645,plain,
    ( r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1644])).

cnf(c_1649,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1645,c_44,c_42])).

cnf(c_1650,plain,
    ( r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1649])).

cnf(c_7850,plain,
    ( r3_waybel_9(sK7,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_1651,plain,
    ( r3_waybel_9(sK7,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_7846,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1857])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7869,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8666,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7846,c_7869])).

cnf(c_9100,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | r3_waybel_9(sK7,X0,X1) = iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7850,c_1651,c_8666])).

cnf(c_9101,plain,
    ( r3_waybel_9(sK7,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9100])).

cnf(c_12695,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X1,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1)))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,X0,k10_yellow_6(sK7,X1)),k10_yellow_6(sK7,X2)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12688,c_9101])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f93])).

cnf(c_1612,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_43])).

cnf(c_1613,plain,
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
    inference(unflattening,[status(thm)],[c_1612])).

cnf(c_1615,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,X2,X1)
    | ~ m2_yellow_6(X0,sK7,X2)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1613,c_44,c_42])).

cnf(c_1616,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,X2,X1)
    | ~ m2_yellow_6(X0,sK7,X2)
    | ~ l1_waybel_0(X2,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1615])).

cnf(c_7851,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | r3_waybel_9(sK7,X2,X1) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_13099,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | m2_yellow_6(X1,sK7,X2) != iProver_top
    | r1_waybel_0(sK7,X0,sK3(sK7,X3,sK1(sK7,X0,k10_yellow_6(sK7,X1)))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,X0,k10_yellow_6(sK7,X1)),k10_yellow_6(sK7,X3)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X3) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12695,c_7851])).

cnf(c_13596,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | m2_yellow_6(X1,sK7,X3) != iProver_top
    | m2_yellow_6(X3,sK7,X2) != iProver_top
    | r1_waybel_0(sK7,X0,sK3(sK7,X4,sK1(sK7,X0,k10_yellow_6(sK7,X1)))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X4,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,X0,k10_yellow_6(sK7,X1)),k10_yellow_6(sK7,X4)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X4) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X4) != iProver_top
    | v4_orders_2(X3) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X4) != iProver_top
    | v7_waybel_0(X3) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13099,c_7851])).

cnf(c_13767,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | r1_waybel_0(sK7,X1,sK3(sK7,X3,sK1(sK7,X1,k10_yellow_6(sK7,X0)))) = iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X3)) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X3) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X3) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_13596])).

cnf(c_1858,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1857])).

cnf(c_13776,plain,
    ( m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | r1_waybel_0(sK7,X1,sK3(sK7,X3,sK1(sK7,X1,k10_yellow_6(sK7,X0)))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X3)) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X3) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X3) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13767,c_1858])).

cnf(c_13777,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | r1_waybel_0(sK7,X1,sK3(sK7,X3,sK1(sK7,X1,k10_yellow_6(sK7,X0)))) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X3,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X3)) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X3) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X3) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X3) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13776])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f114])).

cnf(c_1713,plain,
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
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_43])).

cnf(c_1714,plain,
    ( ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1713])).

cnf(c_1718,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1714,c_44,c_42])).

cnf(c_1719,plain,
    ( ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1718])).

cnf(c_1875,plain,
    ( ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k10_yellow_6(sK7,X0))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1857,c_1719])).

cnf(c_7844,plain,
    ( r1_waybel_0(sK7,X0,sK3(sK7,X0,X1)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1875])).

cnf(c_13782,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13777,c_7844])).

cnf(c_14281,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | r3_waybel_9(sK7,X1,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13782,c_9101])).

cnf(c_27866,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | r3_waybel_9(sK7,X0,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | m2_yellow_6(X1,sK7,sK9(X2)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7842,c_14281])).

cnf(c_29,plain,
    ( ~ r3_waybel_9(X0,sK6(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1495,plain,
    ( ~ r3_waybel_9(X0,sK6(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_43])).

cnf(c_1496,plain,
    ( ~ r3_waybel_9(sK7,sK6(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1495])).

cnf(c_1500,plain,
    ( ~ r3_waybel_9(sK7,sK6(sK7),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1496,c_44,c_42])).

cnf(c_7855,plain,
    ( r3_waybel_9(sK7,sK6(sK7),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1500])).

cnf(c_27889,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X1),sK7) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(X1)) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X1)) != iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(X1)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27866,c_7855])).

cnf(c_34,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK6(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1425,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK6(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_43])).

cnf(c_1426,plain,
    ( v1_compts_1(sK7)
    | ~ v2_struct_0(sK6(sK7))
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1425])).

cnf(c_1428,plain,
    ( v1_compts_1(sK7)
    | ~ v2_struct_0(sK6(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1426,c_44,c_43,c_42,c_62])).

cnf(c_1430,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_33,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK6(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1439,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK6(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_43])).

cnf(c_1440,plain,
    ( v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | v4_orders_2(sK6(sK7))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1439])).

cnf(c_1442,plain,
    ( v4_orders_2(sK6(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1440,c_44,c_42])).

cnf(c_1443,plain,
    ( v1_compts_1(sK7)
    | v4_orders_2(sK6(sK7)) ),
    inference(renaming,[status(thm)],[c_1442])).

cnf(c_1444,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v4_orders_2(sK6(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_32,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK6(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1453,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK6(X0))
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_43])).

cnf(c_1454,plain,
    ( v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | v7_waybel_0(sK6(sK7))
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1453])).

cnf(c_1456,plain,
    ( v7_waybel_0(sK6(sK7))
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1454,c_44,c_42])).

cnf(c_1457,plain,
    ( v1_compts_1(sK7)
    | v7_waybel_0(sK6(sK7)) ),
    inference(renaming,[status(thm)],[c_1456])).

cnf(c_1458,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v7_waybel_0(sK6(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_31,plain,
    ( l1_waybel_0(sK6(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1467,plain,
    ( l1_waybel_0(sK6(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_43])).

cnf(c_1468,plain,
    ( l1_waybel_0(sK6(sK7),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1467])).

cnf(c_1470,plain,
    ( l1_waybel_0(sK6(sK7),sK7)
    | v1_compts_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1468,c_44,c_42])).

cnf(c_1472,plain,
    ( l1_waybel_0(sK6(sK7),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_7874,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_7871,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8665,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7871,c_7869])).

cnf(c_9698,plain,
    ( m1_subset_1(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7874,c_8665])).

cnf(c_9106,plain,
    ( r3_waybel_9(sK7,X0,sK0(k10_yellow_6(sK7,X0),X1)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | r1_tarski(k10_yellow_6(sK7,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7874,c_9101])).

cnf(c_10038,plain,
    ( l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK7,sK6(sK7)),X0),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9106,c_7855])).

cnf(c_10968,plain,
    ( v1_compts_1(sK7) = iProver_top
    | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK7,sK6(sK7)),X0),u1_struct_0(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10038,c_1430,c_1444,c_1458,c_1472])).

cnf(c_10969,plain,
    ( m1_subset_1(sK0(k10_yellow_6(sK7,sK6(sK7)),X0),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_10968])).

cnf(c_10974,plain,
    ( r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
    | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_9698,c_10969])).

cnf(c_10030,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(sK0(k10_yellow_6(sK7,X0),X1),u1_struct_0(sK7)) = iProver_top
    | r1_tarski(k10_yellow_6(sK7,X0),X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7874,c_8666])).

cnf(c_11738,plain,
    ( l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10030,c_10969])).

cnf(c_18950,plain,
    ( r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10974,c_1430,c_1444,c_1458,c_1472,c_11738])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_7868,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14278,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | r1_tarski(k10_yellow_6(sK7,X1),sK1(sK7,X1,k10_yellow_6(sK7,X0))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13782,c_7868])).

cnf(c_28298,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X1),sK7) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(X1)) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X1)) != iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(X1)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18950,c_14278])).

cnf(c_29103,plain,
    ( v7_waybel_0(sK9(X1)) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(sK9(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | l1_waybel_0(sK9(X1),sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27889,c_1430,c_1444,c_1458,c_1472,c_28298])).

cnf(c_29104,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X1),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_29103])).

cnf(c_29109,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X1),sK7) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(X1)) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X1)) != iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(X1)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7842,c_29104])).

cnf(c_29117,plain,
    ( v7_waybel_0(sK9(X1)) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(sK9(X1)) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | l1_waybel_0(sK9(X1),sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29109,c_1430,c_1444,c_1458,c_1472,c_1858])).

cnf(c_29118,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X1),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(X1)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X1)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_29117])).

cnf(c_29127,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_29118,c_7851])).

cnf(c_29142,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7842,c_29127])).

cnf(c_40041,plain,
    ( v7_waybel_0(sK9(X2)) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29142,c_1430,c_1444,c_1458,c_1472,c_1858])).

cnf(c_40042,plain,
    ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X2),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK9(X2)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK9(X2)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK9(X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_40041])).

cnf(c_40047,plain,
    ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
    | m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(X0),sK7) != iProver_top
    | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(X0)) = iProver_top
    | v2_struct_0(sK9(sK9(X0))) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(X0)) != iProver_top
    | v4_orders_2(sK9(sK9(X0))) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(X0)) != iProver_top
    | v7_waybel_0(sK9(sK9(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_40042])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_17,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_841,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_842,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_2131,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_842,c_42])).

cnf(c_2132,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | l1_waybel_0(X0,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2131])).

cnf(c_2134,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2132,c_44])).

cnf(c_2135,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | l1_waybel_0(X0,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2134])).

cnf(c_2136,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_18,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_813,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_814,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_813])).

cnf(c_2157,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_814,c_42])).

cnf(c_2158,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2157])).

cnf(c_2160,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2158,c_44])).

cnf(c_2161,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_2160])).

cnf(c_2162,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_19,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_785,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_786,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_785])).

cnf(c_2183,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_786,c_42])).

cnf(c_2184,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2183])).

cnf(c_2186,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2184,c_44])).

cnf(c_2187,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2186])).

cnf(c_2188,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2187])).

cnf(c_20,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_757,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X3)
    | X1 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_758,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_2209,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_758,c_42])).

cnf(c_2210,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2209])).

cnf(c_2212,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK7)
    | ~ m2_yellow_6(X0,sK7,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2210,c_44])).

cnf(c_2213,plain,
    ( ~ m2_yellow_6(X0,sK7,X1)
    | ~ l1_waybel_0(X1,sK7)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2212])).

cnf(c_2214,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_2692,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | v1_compts_1(sK7)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X0 != X1
    | sK9(X1) != X2
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_2213])).

cnf(c_2693,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2692])).

cnf(c_2694,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2693])).

cnf(c_2716,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X0 != X1
    | sK9(X1) != X2
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_2187])).

cnf(c_2717,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2716])).

cnf(c_2718,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(X0)) = iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2717])).

cnf(c_2740,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X2)
    | X0 != X1
    | sK9(X1) != X2
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_2161])).

cnf(c_2741,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK9(X0)) ),
    inference(unflattening,[status(thm)],[c_2740])).

cnf(c_2742,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2741])).

cnf(c_2764,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(X1,sK7)
    | l1_waybel_0(X2,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(X1)
    | X0 != X1
    | sK9(X1) != X2
    | sK7 != sK7 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_2135])).

cnf(c_2765,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2764])).

cnf(c_2766,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK9(X0),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2765])).

cnf(c_7840,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_8820,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK9(X0),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_7840])).

cnf(c_7839,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_8581,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_7839])).

cnf(c_8823,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X0)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(X0)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(X0)) != iProver_top
    | v7_waybel_0(sK9(sK9(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8820,c_8581])).

cnf(c_10979,plain,
    ( v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(sK9(sK9(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8823,c_2694,c_2718,c_2742])).

cnf(c_10980,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(sK9(X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10979])).

cnf(c_7838,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2187])).

cnf(c_8578,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(X0)) = iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_7838])).

cnf(c_8824,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X0)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(X0)) != iProver_top
    | v4_orders_2(sK9(sK9(X0))) = iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8820,c_8578])).

cnf(c_11007,plain,
    ( v7_waybel_0(X0) != iProver_top
    | v4_orders_2(sK9(sK9(X0))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v4_orders_2(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8824,c_2694,c_2718,c_2742])).

cnf(c_11008,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(sK9(X0))) = iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11007])).

cnf(c_7837,plain,
    ( m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_8250,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_7837])).

cnf(c_8825,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(X0)) = iProver_top
    | v2_struct_0(sK9(sK9(X0))) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK9(X0)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK9(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8820,c_8250])).

cnf(c_11409,plain,
    ( v7_waybel_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v2_struct_0(sK9(sK9(X0))) != iProver_top
    | v4_orders_2(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8825,c_2694,c_2718,c_2742])).

cnf(c_11410,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(sK9(X0))) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11409])).

cnf(c_40056,plain,
    ( v4_orders_2(X1) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
    | m2_yellow_6(X0,sK7,X1) != iProver_top
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
    | k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
    | l1_waybel_0(X1,sK7) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_40047,c_2136,c_2162,c_2188,c_2214,c_2694,c_2718,c_2742,c_2766,c_10980,c_11008,c_11410])).

cnf(c_40057,plain,
    ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
    | m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_40056])).

cnf(c_40064,plain,
    ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0)))),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_40057,c_7851])).

cnf(c_42914,plain,
    ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(X0))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7842,c_40064])).

cnf(c_42929,plain,
    ( v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(X0))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42914,c_1430,c_1444,c_1458,c_1472])).

cnf(c_42930,plain,
    ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | m2_yellow_6(X2,sK7,X1) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(X0))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_42929])).

cnf(c_42933,plain,
    ( k10_yellow_6(sK7,sK9(sK9(sK9(X0)))) = k10_yellow_6(sK7,sK6(sK7))
    | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(sK9(X0)))))) = iProver_top
    | m2_yellow_6(X0,sK7,X1) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(sK9(sK9(X0))),sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(sK9(X0)))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_42930])).

cnf(c_8180,plain,
    ( m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7))
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_8238,plain,
    ( m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7)) = iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8180])).

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
    inference(cnf_transformation,[],[f90])).

cnf(c_40,negated_conjecture,
    ( v3_yellow_6(sK9(X0),sK7)
    | ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_939,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_40])).

cnf(c_940,plain,
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
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_944,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_940,c_44,c_43,c_42])).

cnf(c_945,plain,
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
    inference(renaming,[status(thm)],[c_944])).

cnf(c_2947,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK9(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK9(X0))
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2693,c_945])).

cnf(c_2958,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK9(X0))
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2717,c_2947])).

cnf(c_2969,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK9(X0),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2741,c_2958])).

cnf(c_2975,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2765,c_2969])).

cnf(c_8300,plain,
    ( ~ l1_waybel_0(sK6(sK7),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7))
    | k10_yellow_6(sK7,sK9(sK6(sK7))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2975])).

cnf(c_8301,plain,
    ( k10_yellow_6(sK7,sK9(sK6(sK7))) != k1_xboole_0
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8300])).

cnf(c_8113,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_tarski(X0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8437,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ r1_tarski(k1_xboole_0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_8113])).

cnf(c_8438,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | r1_tarski(k1_xboole_0,u1_struct_0(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8437])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8573,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK7)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8574,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8573])).

cnf(c_8153,plain,
    ( ~ m2_yellow_6(X0,sK7,sK6(sK7))
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_8599,plain,
    ( ~ m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7))
    | l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_8153])).

cnf(c_8600,plain,
    ( m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) = iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8599])).

cnf(c_7857,plain,
    ( l1_waybel_0(sK6(sK7),sK7) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_8729,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7857,c_8578])).

cnf(c_9868,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8729,c_1430,c_1444,c_1458])).

cnf(c_8733,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) = iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7857,c_8581])).

cnf(c_9873,plain,
    ( v7_waybel_0(sK9(sK6(sK7))) = iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8733,c_1430,c_1444,c_1458])).

cnf(c_9874,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9873])).

cnf(c_9036,plain,
    ( ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),X0),u1_struct_0(sK7))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7)))
    | k10_yellow_6(sK7,sK9(sK6(sK7))) = X0 ),
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_9946,plain,
    ( ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7)))
    | k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9036])).

cnf(c_9966,plain,
    ( k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9946])).

cnf(c_8420,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) != iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7857,c_8250])).

cnf(c_9978,plain,
    ( v2_struct_0(sK9(sK6(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8420,c_1430,c_1444,c_1458])).

cnf(c_9979,plain,
    ( v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9978])).

cnf(c_11583,plain,
    ( r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11584,plain,
    ( r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11583])).

cnf(c_9242,plain,
    ( r3_waybel_9(sK7,sK6(X0),X1)
    | ~ l1_waybel_0(sK6(X0),sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | ~ r2_hidden(X1,k10_yellow_6(sK7,sK6(X0)))
    | v2_struct_0(sK6(X0))
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(sK6(X0)) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_12475,plain,
    ( r3_waybel_9(sK7,sK6(X0),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | ~ l1_waybel_0(sK6(X0),sK7)
    | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | ~ r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(X0)))
    | v2_struct_0(sK6(X0))
    | ~ v4_orders_2(sK6(X0))
    | ~ v7_waybel_0(sK6(X0)) ),
    inference(instantiation,[status(thm)],[c_9242])).

cnf(c_12501,plain,
    ( r3_waybel_9(sK7,sK6(X0),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
    | l1_waybel_0(sK6(X0),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(X0))) != iProver_top
    | v2_struct_0(sK6(X0)) = iProver_top
    | v4_orders_2(sK6(X0)) != iProver_top
    | v7_waybel_0(sK6(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12475])).

cnf(c_12503,plain,
    ( r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(sK7))) != iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12501])).

cnf(c_12550,plain,
    ( ~ r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | v1_compts_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_12554,plain,
    ( r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12550])).

cnf(c_9037,plain,
    ( r3_waybel_9(sK7,sK9(sK6(sK7)),X0)
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | ~ r2_hidden(X0,k10_yellow_6(sK7,sK9(sK6(sK7))))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_12539,plain,
    ( r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | ~ r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7))))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_9037])).

cnf(c_12576,plain,
    ( r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7)))) != iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12539])).

cnf(c_9030,plain,
    ( ~ r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),X0))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(X0,k10_yellow_6(sK7,sK9(sK6(sK7))))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_12537,plain,
    ( ~ r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7))))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_9030])).

cnf(c_12580,plain,
    ( r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))) != iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7)))) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12537])).

cnf(c_9031,plain,
    ( m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),X0),sK7,X0)
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(X0,u1_struct_0(sK7))
    | r2_hidden(X0,k10_yellow_6(sK7,sK9(sK6(sK7))))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_12536,plain,
    ( m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7))))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_9031])).

cnf(c_12582,plain,
    ( m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7)))) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12536])).

cnf(c_8171,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | r3_waybel_9(sK7,sK6(sK7),X1)
    | ~ m2_yellow_6(X0,sK7,sK6(sK7))
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_12477,plain,
    ( ~ r3_waybel_9(sK7,X0,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | ~ m2_yellow_6(X0,sK7,sK6(sK7))
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_8171])).

cnf(c_20404,plain,
    ( ~ r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | ~ m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7))
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_12477])).

cnf(c_20405,plain,
    ( r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
    | r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
    | m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20404])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8767,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k10_yellow_6(sK7,sK6(sK7)))
    | ~ r1_tarski(X1,k10_yellow_6(sK7,sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_10153,plain,
    ( r2_hidden(X0,k10_yellow_6(sK7,sK6(sK7)))
    | ~ r2_hidden(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_8767])).

cnf(c_31642,plain,
    ( r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(sK7)))
    | ~ r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_10153])).

cnf(c_31643,plain,
    ( r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(sK7))) = iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31642])).

cnf(c_8997,plain,
    ( ~ m1_connsp_2(X0,sK7,sK1(sK7,sK9(sK6(sK7)),X1))
    | r1_waybel_0(sK7,sK9(sK6(sK7)),X0)
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),X1),X1)
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7)))
    | k10_yellow_6(sK7,sK9(sK6(sK7))) = X1 ),
    inference(instantiation,[status(thm)],[c_1965])).

cnf(c_9916,plain,
    ( ~ m1_connsp_2(X0,sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | r1_waybel_0(sK7,sK9(sK6(sK7)),X0)
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0)
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7)))
    | k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8997])).

cnf(c_43239,plain,
    ( ~ m1_connsp_2(sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
    | r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0)
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7)))
    | k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9916])).

cnf(c_43242,plain,
    ( k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0
    | m1_connsp_2(sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
    | r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))) = iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43239])).

cnf(c_43244,plain,
    ( k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0
    | m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
    | r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))) = iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43242])).

cnf(c_44216,plain,
    ( v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42933,c_1430,c_1444,c_1458,c_1472,c_8238,c_8301,c_8438,c_8574,c_8600,c_9868,c_9874,c_9966,c_9979,c_11584,c_12503,c_12554,c_12576,c_12580,c_12582,c_20405,c_31643,c_43244])).

cnf(c_27,plain,
    ( r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1516,plain,
    ( r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_43])).

cnf(c_1517,plain,
    ( r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1516])).

cnf(c_1521,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1517,c_44,c_42])).

cnf(c_1522,plain,
    ( r3_waybel_9(sK7,X0,sK5(sK7,X0))
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1521])).

cnf(c_7854,plain,
    ( r3_waybel_9(sK7,X0,sK5(sK7,X0)) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_26,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK4(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1546,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK4(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_43])).

cnf(c_1547,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1546])).

cnf(c_1551,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1547,c_44,c_42])).

cnf(c_1552,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1551])).

cnf(c_7853,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0) = iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1552])).

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
    inference(cnf_transformation,[],[f91])).

cnf(c_35,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ v3_yellow_6(X0,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_906,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_907,plain,
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
    inference(unflattening,[status(thm)],[c_906])).

cnf(c_911,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK7)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m2_yellow_6(X0,sK7,sK8)
    | v2_struct_0(X0)
    | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_907,c_44,c_43,c_42])).

cnf(c_912,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(X0,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_911])).

cnf(c_7861,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_45,plain,
    ( v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_46,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_47,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_54,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_55,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v4_orders_2(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( ~ v1_compts_1(sK7)
    | v7_waybel_0(sK8) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_56,plain,
    ( v1_compts_1(sK7) != iProver_top
    | v7_waybel_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_57,plain,
    ( l1_waybel_0(sK8,sK7) = iProver_top
    | v1_compts_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_908,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_7970,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_7971,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7970])).

cnf(c_7975,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_7976,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7975])).

cnf(c_7980,plain,
    ( ~ m2_yellow_6(X0,sK7,sK8)
    | ~ l1_waybel_0(sK8,sK7)
    | v2_struct_0(sK8)
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_7981,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7980])).

cnf(c_9091,plain,
    ( m2_yellow_6(X0,sK7,sK8) != iProver_top
    | k10_yellow_6(sK7,X0) = k1_xboole_0
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7861,c_54,c_55,c_56,c_57,c_913,c_7971,c_7976,c_7981])).

cnf(c_9092,plain,
    ( k10_yellow_6(sK7,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK7,sK8) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9091])).

cnf(c_9379,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK4(sK7,sK8,X0)) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7853,c_9092])).

cnf(c_11528,plain,
    ( v2_struct_0(sK4(sK7,sK8,X0)) = iProver_top
    | v1_compts_1(sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9379,c_54,c_55,c_56,c_57])).

cnf(c_11529,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK4(sK7,sK8,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11528])).

cnf(c_9383,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4(sK7,X0,X1)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7853,c_7837])).

cnf(c_11534,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_11529,c_9383])).

cnf(c_23987,plain,
    ( v1_compts_1(sK7) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11534,c_54,c_55,c_56,c_57])).

cnf(c_23988,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
    | r3_waybel_9(sK7,sK8,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_23987])).

cnf(c_23993,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_7854,c_23988])).

cnf(c_28,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1821,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_43])).

cnf(c_1822,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1821])).

cnf(c_1826,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1822,c_44,c_42])).

cnf(c_1827,plain,
    ( ~ l1_waybel_0(X0,sK7)
    | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1826])).

cnf(c_7956,plain,
    ( ~ l1_waybel_0(sK8,sK7)
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
    | ~ v1_compts_1(sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_7957,plain,
    ( l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) = iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7956])).

cnf(c_24424,plain,
    ( v1_compts_1(sK7) != iProver_top
    | k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23993,c_54,c_55,c_56,c_57,c_7957])).

cnf(c_24425,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0
    | v1_compts_1(sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_24424])).

cnf(c_44220,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44216,c_24425])).

cnf(c_25,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1579,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_43])).

cnf(c_1580,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1)))
    | v2_struct_0(X0)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_1579])).

cnf(c_1584,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1580,c_44,c_42])).

cnf(c_1585,plain,
    ( ~ r3_waybel_9(sK7,X0,X1)
    | ~ l1_waybel_0(X0,sK7)
    | ~ m1_subset_1(X1,u1_struct_0(sK7))
    | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1584])).

cnf(c_7852,plain,
    ( r3_waybel_9(sK7,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1585])).

cnf(c_47030,plain,
    ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) != iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,sK8),k1_xboole_0) = iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_44220,c_7852])).

cnf(c_7967,plain,
    ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
    | ~ l1_waybel_0(sK8,sK7)
    | ~ v1_compts_1(sK7)
    | v2_struct_0(sK8)
    | ~ v4_orders_2(sK8)
    | ~ v7_waybel_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1522])).

cnf(c_7968,plain,
    ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
    | l1_waybel_0(sK8,sK7) != iProver_top
    | v1_compts_1(sK7) != iProver_top
    | v2_struct_0(sK8) = iProver_top
    | v4_orders_2(sK8) != iProver_top
    | v7_waybel_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7967])).

cnf(c_47125,plain,
    ( r2_hidden(sK5(sK7,sK8),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47030,c_54,c_55,c_56,c_57,c_1430,c_1444,c_1458,c_1472,c_7957,c_7968,c_8238,c_8301,c_8438,c_8574,c_8600,c_9868,c_9874,c_9966,c_9979,c_11584,c_12503,c_12554,c_12576,c_12580,c_12582,c_20405,c_31643,c_43244])).

cnf(c_14283,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13782,c_7855])).

cnf(c_9000,plain,
    ( ~ m2_yellow_6(X0,sK7,sK9(sK6(sK7)))
    | l1_waybel_0(X0,sK7)
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_9001,plain,
    ( m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9000])).

cnf(c_8999,plain,
    ( ~ m2_yellow_6(X0,sK7,sK9(sK6(sK7)))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_9005,plain,
    ( m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8999])).

cnf(c_8998,plain,
    ( ~ m2_yellow_6(X0,sK7,sK9(sK6(sK7)))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | v2_struct_0(sK9(sK6(sK7)))
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_9009,plain,
    ( m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8998])).

cnf(c_14331,plain,
    ( v4_orders_2(X1) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14283,c_1430,c_1444,c_1458,c_1472,c_8238,c_8420,c_8600,c_8733,c_9001,c_9005,c_9009,c_9868])).

cnf(c_14332,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_14331])).

cnf(c_14341,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X1,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(X1,sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14332,c_9101])).

cnf(c_14359,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X0,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7842,c_14341])).

cnf(c_14510,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14359,c_7851])).

cnf(c_16710,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
    | m2_yellow_6(X0,sK7,X2) != iProver_top
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(X2,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7842,c_14510])).

cnf(c_16765,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16710,c_7855])).

cnf(c_8154,plain,
    ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(X0,sK7) = iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8153])).

cnf(c_8152,plain,
    ( ~ m2_yellow_6(X0,sK7,sK6(sK7))
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | v2_struct_0(sK6(sK7))
    | ~ v4_orders_2(sK6(sK7))
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_8158,plain,
    ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8152])).

cnf(c_8151,plain,
    ( ~ m2_yellow_6(X0,sK7,sK6(sK7))
    | ~ l1_waybel_0(sK6(sK7),sK7)
    | v2_struct_0(sK6(sK7))
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK6(sK7))
    | ~ v7_waybel_0(sK6(sK7)) ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_8162,plain,
    ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8151])).

cnf(c_16772,plain,
    ( v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v1_compts_1(sK7) = iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
    | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16765,c_1430,c_1444,c_1458,c_1472,c_8154,c_8158,c_8162])).

cnf(c_16773,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_16772])).

cnf(c_16778,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7842,c_16773])).

cnf(c_17023,plain,
    ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16778,c_1430,c_1444,c_1458,c_1472,c_8154,c_8158,c_8162])).

cnf(c_17024,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
    | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_17023])).

cnf(c_17030,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(X0,sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7846,c_17024])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7870,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8414,plain,
    ( l1_waybel_0(X0,sK7) != iProver_top
    | r1_tarski(k10_yellow_6(sK7,X0),u1_struct_0(sK7)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7846,c_7870])).

cnf(c_17029,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
    | r1_tarski(k10_yellow_6(sK7,X0),u1_struct_0(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7871,c_17024])).

cnf(c_17038,plain,
    ( m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17030,c_1430,c_1444,c_1458,c_1472,c_8238,c_8420,c_8600,c_8733,c_9001,c_9005,c_9009,c_9868])).

cnf(c_17039,plain,
    ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
    | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
    | m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_17038])).

cnf(c_17044,plain,
    ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,X0)
    | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK9(sK9(sK6(sK7)))) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_17039])).

cnf(c_9028,plain,
    ( m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7)))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | v1_compts_1(sK7)
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_9086,plain,
    ( m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7))) = iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9028])).

cnf(c_10947,plain,
    ( ~ m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,X0)
    | ~ l1_waybel_0(X0,sK7)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK9(sK9(sK6(sK7))))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_16686,plain,
    ( ~ m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7)))
    | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
    | ~ v2_struct_0(sK9(sK9(sK6(sK7))))
    | v2_struct_0(sK9(sK6(sK7)))
    | ~ v4_orders_2(sK9(sK6(sK7)))
    | ~ v7_waybel_0(sK9(sK6(sK7))) ),
    inference(instantiation,[status(thm)],[c_10947])).

cnf(c_16687,plain,
    ( m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7))) != iProver_top
    | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
    | v2_struct_0(sK9(sK9(sK6(sK7)))) != iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v4_orders_2(sK9(sK6(sK7))) != iProver_top
    | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16686])).

cnf(c_17814,plain,
    ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,X0)
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17044,c_1430,c_1444,c_1458,c_1472,c_8238,c_8420,c_8600,c_8733,c_9086,c_9868,c_16687])).

cnf(c_17815,plain,
    ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,X0)
    | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_17814])).

cnf(c_17820,plain,
    ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7)))
    | l1_waybel_0(sK6(sK7),sK7) != iProver_top
    | v1_compts_1(sK7) = iProver_top
    | v2_struct_0(sK9(sK6(sK7))) = iProver_top
    | v2_struct_0(sK6(sK7)) = iProver_top
    | v4_orders_2(sK6(sK7)) != iProver_top
    | v7_waybel_0(sK6(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7863,c_17815])).

cnf(c_17824,plain,
    ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7)))
    | v1_compts_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17820,c_1430,c_1444,c_1458,c_1472,c_9979])).

cnf(c_24429,plain,
    ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0
    | k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7))) ),
    inference(superposition,[status(thm)],[c_17824,c_24425])).

cnf(c_24559,plain,
    ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7)))
    | l1_waybel_0(sK4(sK7,sK8,sK5(sK7,sK8)),sK7) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
    | v2_struct_0(sK4(sK7,sK8,sK5(sK7,sK8))) = iProver_top
    | v4_orders_2(sK4(sK7,sK8,sK5(sK7,sK8))) != iProver_top
    | v7_waybel_0(sK4(sK7,sK8,sK5(sK7,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24429,c_7846])).

cnf(c_24800,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24559,c_8438,c_8574])).

cnf(c_24805,plain,
    ( m1_subset_1(X0,u1_struct_0(sK7)) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24800,c_7869])).

cnf(c_727,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_728,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_729,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_24813,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24805,c_729])).

cnf(c_47132,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_47125,c_24813])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.85/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.85/2.99  
% 19.85/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.85/2.99  
% 19.85/2.99  ------  iProver source info
% 19.85/2.99  
% 19.85/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.85/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.85/2.99  git: non_committed_changes: false
% 19.85/2.99  git: last_make_outside_of_git: false
% 19.85/2.99  
% 19.85/2.99  ------ 
% 19.85/2.99  
% 19.85/2.99  ------ Input Options
% 19.85/2.99  
% 19.85/2.99  --out_options                           all
% 19.85/2.99  --tptp_safe_out                         true
% 19.85/2.99  --problem_path                          ""
% 19.85/2.99  --include_path                          ""
% 19.85/2.99  --clausifier                            res/vclausify_rel
% 19.85/2.99  --clausifier_options                    ""
% 19.85/2.99  --stdin                                 false
% 19.85/2.99  --stats_out                             all
% 19.85/2.99  
% 19.85/2.99  ------ General Options
% 19.85/2.99  
% 19.85/2.99  --fof                                   false
% 19.85/2.99  --time_out_real                         305.
% 19.85/2.99  --time_out_virtual                      -1.
% 19.85/2.99  --symbol_type_check                     false
% 19.85/2.99  --clausify_out                          false
% 19.85/2.99  --sig_cnt_out                           false
% 19.85/2.99  --trig_cnt_out                          false
% 19.85/2.99  --trig_cnt_out_tolerance                1.
% 19.85/2.99  --trig_cnt_out_sk_spl                   false
% 19.85/2.99  --abstr_cl_out                          false
% 19.85/2.99  
% 19.85/2.99  ------ Global Options
% 19.85/2.99  
% 19.85/2.99  --schedule                              default
% 19.85/2.99  --add_important_lit                     false
% 19.85/2.99  --prop_solver_per_cl                    1000
% 19.85/2.99  --min_unsat_core                        false
% 19.85/2.99  --soft_assumptions                      false
% 19.85/2.99  --soft_lemma_size                       3
% 19.85/2.99  --prop_impl_unit_size                   0
% 19.85/2.99  --prop_impl_unit                        []
% 19.85/2.99  --share_sel_clauses                     true
% 19.85/2.99  --reset_solvers                         false
% 19.85/2.99  --bc_imp_inh                            [conj_cone]
% 19.85/2.99  --conj_cone_tolerance                   3.
% 19.85/2.99  --extra_neg_conj                        none
% 19.85/2.99  --large_theory_mode                     true
% 19.85/2.99  --prolific_symb_bound                   200
% 19.85/2.99  --lt_threshold                          2000
% 19.85/2.99  --clause_weak_htbl                      true
% 19.85/2.99  --gc_record_bc_elim                     false
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing Options
% 19.85/2.99  
% 19.85/2.99  --preprocessing_flag                    true
% 19.85/2.99  --time_out_prep_mult                    0.1
% 19.85/2.99  --splitting_mode                        input
% 19.85/2.99  --splitting_grd                         true
% 19.85/2.99  --splitting_cvd                         false
% 19.85/2.99  --splitting_cvd_svl                     false
% 19.85/2.99  --splitting_nvd                         32
% 19.85/2.99  --sub_typing                            true
% 19.85/2.99  --prep_gs_sim                           true
% 19.85/2.99  --prep_unflatten                        true
% 19.85/2.99  --prep_res_sim                          true
% 19.85/2.99  --prep_upred                            true
% 19.85/2.99  --prep_sem_filter                       exhaustive
% 19.85/2.99  --prep_sem_filter_out                   false
% 19.85/2.99  --pred_elim                             true
% 19.85/2.99  --res_sim_input                         true
% 19.85/2.99  --eq_ax_congr_red                       true
% 19.85/2.99  --pure_diseq_elim                       true
% 19.85/2.99  --brand_transform                       false
% 19.85/2.99  --non_eq_to_eq                          false
% 19.85/2.99  --prep_def_merge                        true
% 19.85/2.99  --prep_def_merge_prop_impl              false
% 19.85/2.99  --prep_def_merge_mbd                    true
% 19.85/2.99  --prep_def_merge_tr_red                 false
% 19.85/2.99  --prep_def_merge_tr_cl                  false
% 19.85/2.99  --smt_preprocessing                     true
% 19.85/2.99  --smt_ac_axioms                         fast
% 19.85/2.99  --preprocessed_out                      false
% 19.85/2.99  --preprocessed_stats                    false
% 19.85/2.99  
% 19.85/2.99  ------ Abstraction refinement Options
% 19.85/2.99  
% 19.85/2.99  --abstr_ref                             []
% 19.85/2.99  --abstr_ref_prep                        false
% 19.85/2.99  --abstr_ref_until_sat                   false
% 19.85/2.99  --abstr_ref_sig_restrict                funpre
% 19.85/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.85/2.99  --abstr_ref_under                       []
% 19.85/2.99  
% 19.85/2.99  ------ SAT Options
% 19.85/2.99  
% 19.85/2.99  --sat_mode                              false
% 19.85/2.99  --sat_fm_restart_options                ""
% 19.85/2.99  --sat_gr_def                            false
% 19.85/2.99  --sat_epr_types                         true
% 19.85/2.99  --sat_non_cyclic_types                  false
% 19.85/2.99  --sat_finite_models                     false
% 19.85/2.99  --sat_fm_lemmas                         false
% 19.85/2.99  --sat_fm_prep                           false
% 19.85/2.99  --sat_fm_uc_incr                        true
% 19.85/2.99  --sat_out_model                         small
% 19.85/2.99  --sat_out_clauses                       false
% 19.85/2.99  
% 19.85/2.99  ------ QBF Options
% 19.85/2.99  
% 19.85/2.99  --qbf_mode                              false
% 19.85/2.99  --qbf_elim_univ                         false
% 19.85/2.99  --qbf_dom_inst                          none
% 19.85/2.99  --qbf_dom_pre_inst                      false
% 19.85/2.99  --qbf_sk_in                             false
% 19.85/2.99  --qbf_pred_elim                         true
% 19.85/2.99  --qbf_split                             512
% 19.85/2.99  
% 19.85/2.99  ------ BMC1 Options
% 19.85/2.99  
% 19.85/2.99  --bmc1_incremental                      false
% 19.85/2.99  --bmc1_axioms                           reachable_all
% 19.85/2.99  --bmc1_min_bound                        0
% 19.85/2.99  --bmc1_max_bound                        -1
% 19.85/2.99  --bmc1_max_bound_default                -1
% 19.85/2.99  --bmc1_symbol_reachability              true
% 19.85/2.99  --bmc1_property_lemmas                  false
% 19.85/2.99  --bmc1_k_induction                      false
% 19.85/2.99  --bmc1_non_equiv_states                 false
% 19.85/2.99  --bmc1_deadlock                         false
% 19.85/2.99  --bmc1_ucm                              false
% 19.85/2.99  --bmc1_add_unsat_core                   none
% 19.85/2.99  --bmc1_unsat_core_children              false
% 19.85/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.85/2.99  --bmc1_out_stat                         full
% 19.85/2.99  --bmc1_ground_init                      false
% 19.85/2.99  --bmc1_pre_inst_next_state              false
% 19.85/2.99  --bmc1_pre_inst_state                   false
% 19.85/2.99  --bmc1_pre_inst_reach_state             false
% 19.85/2.99  --bmc1_out_unsat_core                   false
% 19.85/2.99  --bmc1_aig_witness_out                  false
% 19.85/2.99  --bmc1_verbose                          false
% 19.85/2.99  --bmc1_dump_clauses_tptp                false
% 19.85/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.85/2.99  --bmc1_dump_file                        -
% 19.85/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.85/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.85/2.99  --bmc1_ucm_extend_mode                  1
% 19.85/2.99  --bmc1_ucm_init_mode                    2
% 19.85/2.99  --bmc1_ucm_cone_mode                    none
% 19.85/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.85/2.99  --bmc1_ucm_relax_model                  4
% 19.85/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.85/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.85/2.99  --bmc1_ucm_layered_model                none
% 19.85/2.99  --bmc1_ucm_max_lemma_size               10
% 19.85/2.99  
% 19.85/2.99  ------ AIG Options
% 19.85/2.99  
% 19.85/2.99  --aig_mode                              false
% 19.85/2.99  
% 19.85/2.99  ------ Instantiation Options
% 19.85/2.99  
% 19.85/2.99  --instantiation_flag                    true
% 19.85/2.99  --inst_sos_flag                         true
% 19.85/2.99  --inst_sos_phase                        true
% 19.85/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel_side                     num_symb
% 19.85/2.99  --inst_solver_per_active                1400
% 19.85/2.99  --inst_solver_calls_frac                1.
% 19.85/2.99  --inst_passive_queue_type               priority_queues
% 19.85/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.85/2.99  --inst_passive_queues_freq              [25;2]
% 19.85/2.99  --inst_dismatching                      true
% 19.85/2.99  --inst_eager_unprocessed_to_passive     true
% 19.85/2.99  --inst_prop_sim_given                   true
% 19.85/2.99  --inst_prop_sim_new                     false
% 19.85/2.99  --inst_subs_new                         false
% 19.85/2.99  --inst_eq_res_simp                      false
% 19.85/2.99  --inst_subs_given                       false
% 19.85/2.99  --inst_orphan_elimination               true
% 19.85/2.99  --inst_learning_loop_flag               true
% 19.85/2.99  --inst_learning_start                   3000
% 19.85/2.99  --inst_learning_factor                  2
% 19.85/2.99  --inst_start_prop_sim_after_learn       3
% 19.85/2.99  --inst_sel_renew                        solver
% 19.85/2.99  --inst_lit_activity_flag                true
% 19.85/2.99  --inst_restr_to_given                   false
% 19.85/2.99  --inst_activity_threshold               500
% 19.85/2.99  --inst_out_proof                        true
% 19.85/2.99  
% 19.85/2.99  ------ Resolution Options
% 19.85/2.99  
% 19.85/2.99  --resolution_flag                       true
% 19.85/2.99  --res_lit_sel                           adaptive
% 19.85/2.99  --res_lit_sel_side                      none
% 19.85/2.99  --res_ordering                          kbo
% 19.85/2.99  --res_to_prop_solver                    active
% 19.85/2.99  --res_prop_simpl_new                    false
% 19.85/2.99  --res_prop_simpl_given                  true
% 19.85/2.99  --res_passive_queue_type                priority_queues
% 19.85/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.85/2.99  --res_passive_queues_freq               [15;5]
% 19.85/2.99  --res_forward_subs                      full
% 19.85/2.99  --res_backward_subs                     full
% 19.85/2.99  --res_forward_subs_resolution           true
% 19.85/2.99  --res_backward_subs_resolution          true
% 19.85/2.99  --res_orphan_elimination                true
% 19.85/2.99  --res_time_limit                        2.
% 19.85/2.99  --res_out_proof                         true
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Options
% 19.85/2.99  
% 19.85/2.99  --superposition_flag                    true
% 19.85/2.99  --sup_passive_queue_type                priority_queues
% 19.85/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.85/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.85/2.99  --demod_completeness_check              fast
% 19.85/2.99  --demod_use_ground                      true
% 19.85/2.99  --sup_to_prop_solver                    passive
% 19.85/2.99  --sup_prop_simpl_new                    true
% 19.85/2.99  --sup_prop_simpl_given                  true
% 19.85/2.99  --sup_fun_splitting                     true
% 19.85/2.99  --sup_smt_interval                      50000
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Simplification Setup
% 19.85/2.99  
% 19.85/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.85/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.85/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.85/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.85/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.85/2.99  --sup_immed_triv                        [TrivRules]
% 19.85/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_immed_bw_main                     []
% 19.85/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.85/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.85/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_input_bw                          []
% 19.85/2.99  
% 19.85/2.99  ------ Combination Options
% 19.85/2.99  
% 19.85/2.99  --comb_res_mult                         3
% 19.85/2.99  --comb_sup_mult                         2
% 19.85/2.99  --comb_inst_mult                        10
% 19.85/2.99  
% 19.85/2.99  ------ Debug Options
% 19.85/2.99  
% 19.85/2.99  --dbg_backtrace                         false
% 19.85/2.99  --dbg_dump_prop_clauses                 false
% 19.85/2.99  --dbg_dump_prop_clauses_file            -
% 19.85/2.99  --dbg_out_stat                          false
% 19.85/2.99  ------ Parsing...
% 19.85/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.85/2.99  ------ Proving...
% 19.85/2.99  ------ Problem Properties 
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  clauses                                 40
% 19.85/2.99  conjectures                             6
% 19.85/2.99  EPR                                     12
% 19.85/2.99  Horn                                    15
% 19.85/2.99  unary                                   2
% 19.85/2.99  binary                                  14
% 19.85/2.99  lits                                    182
% 19.85/2.99  lits eq                                 6
% 19.85/2.99  fd_pure                                 0
% 19.85/2.99  fd_pseudo                               0
% 19.85/2.99  fd_cond                                 0
% 19.85/2.99  fd_pseudo_cond                          4
% 19.85/2.99  AC symbols                              0
% 19.85/2.99  
% 19.85/2.99  ------ Schedule dynamic 5 is on 
% 19.85/2.99  
% 19.85/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  ------ 
% 19.85/2.99  Current options:
% 19.85/2.99  ------ 
% 19.85/2.99  
% 19.85/2.99  ------ Input Options
% 19.85/2.99  
% 19.85/2.99  --out_options                           all
% 19.85/2.99  --tptp_safe_out                         true
% 19.85/2.99  --problem_path                          ""
% 19.85/2.99  --include_path                          ""
% 19.85/2.99  --clausifier                            res/vclausify_rel
% 19.85/2.99  --clausifier_options                    ""
% 19.85/2.99  --stdin                                 false
% 19.85/2.99  --stats_out                             all
% 19.85/2.99  
% 19.85/2.99  ------ General Options
% 19.85/2.99  
% 19.85/2.99  --fof                                   false
% 19.85/2.99  --time_out_real                         305.
% 19.85/2.99  --time_out_virtual                      -1.
% 19.85/2.99  --symbol_type_check                     false
% 19.85/2.99  --clausify_out                          false
% 19.85/2.99  --sig_cnt_out                           false
% 19.85/2.99  --trig_cnt_out                          false
% 19.85/2.99  --trig_cnt_out_tolerance                1.
% 19.85/2.99  --trig_cnt_out_sk_spl                   false
% 19.85/2.99  --abstr_cl_out                          false
% 19.85/2.99  
% 19.85/2.99  ------ Global Options
% 19.85/2.99  
% 19.85/2.99  --schedule                              default
% 19.85/2.99  --add_important_lit                     false
% 19.85/2.99  --prop_solver_per_cl                    1000
% 19.85/2.99  --min_unsat_core                        false
% 19.85/2.99  --soft_assumptions                      false
% 19.85/2.99  --soft_lemma_size                       3
% 19.85/2.99  --prop_impl_unit_size                   0
% 19.85/2.99  --prop_impl_unit                        []
% 19.85/2.99  --share_sel_clauses                     true
% 19.85/2.99  --reset_solvers                         false
% 19.85/2.99  --bc_imp_inh                            [conj_cone]
% 19.85/2.99  --conj_cone_tolerance                   3.
% 19.85/2.99  --extra_neg_conj                        none
% 19.85/2.99  --large_theory_mode                     true
% 19.85/2.99  --prolific_symb_bound                   200
% 19.85/2.99  --lt_threshold                          2000
% 19.85/2.99  --clause_weak_htbl                      true
% 19.85/2.99  --gc_record_bc_elim                     false
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing Options
% 19.85/2.99  
% 19.85/2.99  --preprocessing_flag                    true
% 19.85/2.99  --time_out_prep_mult                    0.1
% 19.85/2.99  --splitting_mode                        input
% 19.85/2.99  --splitting_grd                         true
% 19.85/2.99  --splitting_cvd                         false
% 19.85/2.99  --splitting_cvd_svl                     false
% 19.85/2.99  --splitting_nvd                         32
% 19.85/2.99  --sub_typing                            true
% 19.85/2.99  --prep_gs_sim                           true
% 19.85/2.99  --prep_unflatten                        true
% 19.85/2.99  --prep_res_sim                          true
% 19.85/2.99  --prep_upred                            true
% 19.85/2.99  --prep_sem_filter                       exhaustive
% 19.85/2.99  --prep_sem_filter_out                   false
% 19.85/2.99  --pred_elim                             true
% 19.85/2.99  --res_sim_input                         true
% 19.85/2.99  --eq_ax_congr_red                       true
% 19.85/2.99  --pure_diseq_elim                       true
% 19.85/2.99  --brand_transform                       false
% 19.85/2.99  --non_eq_to_eq                          false
% 19.85/2.99  --prep_def_merge                        true
% 19.85/2.99  --prep_def_merge_prop_impl              false
% 19.85/2.99  --prep_def_merge_mbd                    true
% 19.85/2.99  --prep_def_merge_tr_red                 false
% 19.85/2.99  --prep_def_merge_tr_cl                  false
% 19.85/2.99  --smt_preprocessing                     true
% 19.85/2.99  --smt_ac_axioms                         fast
% 19.85/2.99  --preprocessed_out                      false
% 19.85/2.99  --preprocessed_stats                    false
% 19.85/2.99  
% 19.85/2.99  ------ Abstraction refinement Options
% 19.85/2.99  
% 19.85/2.99  --abstr_ref                             []
% 19.85/2.99  --abstr_ref_prep                        false
% 19.85/2.99  --abstr_ref_until_sat                   false
% 19.85/2.99  --abstr_ref_sig_restrict                funpre
% 19.85/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.85/2.99  --abstr_ref_under                       []
% 19.85/2.99  
% 19.85/2.99  ------ SAT Options
% 19.85/2.99  
% 19.85/2.99  --sat_mode                              false
% 19.85/2.99  --sat_fm_restart_options                ""
% 19.85/2.99  --sat_gr_def                            false
% 19.85/2.99  --sat_epr_types                         true
% 19.85/2.99  --sat_non_cyclic_types                  false
% 19.85/2.99  --sat_finite_models                     false
% 19.85/2.99  --sat_fm_lemmas                         false
% 19.85/2.99  --sat_fm_prep                           false
% 19.85/2.99  --sat_fm_uc_incr                        true
% 19.85/2.99  --sat_out_model                         small
% 19.85/2.99  --sat_out_clauses                       false
% 19.85/2.99  
% 19.85/2.99  ------ QBF Options
% 19.85/2.99  
% 19.85/2.99  --qbf_mode                              false
% 19.85/2.99  --qbf_elim_univ                         false
% 19.85/2.99  --qbf_dom_inst                          none
% 19.85/2.99  --qbf_dom_pre_inst                      false
% 19.85/2.99  --qbf_sk_in                             false
% 19.85/2.99  --qbf_pred_elim                         true
% 19.85/2.99  --qbf_split                             512
% 19.85/2.99  
% 19.85/2.99  ------ BMC1 Options
% 19.85/2.99  
% 19.85/2.99  --bmc1_incremental                      false
% 19.85/2.99  --bmc1_axioms                           reachable_all
% 19.85/2.99  --bmc1_min_bound                        0
% 19.85/2.99  --bmc1_max_bound                        -1
% 19.85/2.99  --bmc1_max_bound_default                -1
% 19.85/2.99  --bmc1_symbol_reachability              true
% 19.85/2.99  --bmc1_property_lemmas                  false
% 19.85/2.99  --bmc1_k_induction                      false
% 19.85/2.99  --bmc1_non_equiv_states                 false
% 19.85/2.99  --bmc1_deadlock                         false
% 19.85/2.99  --bmc1_ucm                              false
% 19.85/2.99  --bmc1_add_unsat_core                   none
% 19.85/2.99  --bmc1_unsat_core_children              false
% 19.85/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.85/2.99  --bmc1_out_stat                         full
% 19.85/2.99  --bmc1_ground_init                      false
% 19.85/2.99  --bmc1_pre_inst_next_state              false
% 19.85/2.99  --bmc1_pre_inst_state                   false
% 19.85/2.99  --bmc1_pre_inst_reach_state             false
% 19.85/2.99  --bmc1_out_unsat_core                   false
% 19.85/2.99  --bmc1_aig_witness_out                  false
% 19.85/2.99  --bmc1_verbose                          false
% 19.85/2.99  --bmc1_dump_clauses_tptp                false
% 19.85/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.85/2.99  --bmc1_dump_file                        -
% 19.85/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.85/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.85/2.99  --bmc1_ucm_extend_mode                  1
% 19.85/2.99  --bmc1_ucm_init_mode                    2
% 19.85/2.99  --bmc1_ucm_cone_mode                    none
% 19.85/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.85/2.99  --bmc1_ucm_relax_model                  4
% 19.85/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.85/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.85/2.99  --bmc1_ucm_layered_model                none
% 19.85/2.99  --bmc1_ucm_max_lemma_size               10
% 19.85/2.99  
% 19.85/2.99  ------ AIG Options
% 19.85/2.99  
% 19.85/2.99  --aig_mode                              false
% 19.85/2.99  
% 19.85/2.99  ------ Instantiation Options
% 19.85/2.99  
% 19.85/2.99  --instantiation_flag                    true
% 19.85/2.99  --inst_sos_flag                         true
% 19.85/2.99  --inst_sos_phase                        true
% 19.85/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel_side                     none
% 19.85/2.99  --inst_solver_per_active                1400
% 19.85/2.99  --inst_solver_calls_frac                1.
% 19.85/2.99  --inst_passive_queue_type               priority_queues
% 19.85/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.85/2.99  --inst_passive_queues_freq              [25;2]
% 19.85/2.99  --inst_dismatching                      true
% 19.85/2.99  --inst_eager_unprocessed_to_passive     true
% 19.85/2.99  --inst_prop_sim_given                   true
% 19.85/2.99  --inst_prop_sim_new                     false
% 19.85/2.99  --inst_subs_new                         false
% 19.85/2.99  --inst_eq_res_simp                      false
% 19.85/2.99  --inst_subs_given                       false
% 19.85/2.99  --inst_orphan_elimination               true
% 19.85/2.99  --inst_learning_loop_flag               true
% 19.85/2.99  --inst_learning_start                   3000
% 19.85/2.99  --inst_learning_factor                  2
% 19.85/2.99  --inst_start_prop_sim_after_learn       3
% 19.85/2.99  --inst_sel_renew                        solver
% 19.85/2.99  --inst_lit_activity_flag                true
% 19.85/2.99  --inst_restr_to_given                   false
% 19.85/2.99  --inst_activity_threshold               500
% 19.85/2.99  --inst_out_proof                        true
% 19.85/2.99  
% 19.85/2.99  ------ Resolution Options
% 19.85/2.99  
% 19.85/2.99  --resolution_flag                       false
% 19.85/2.99  --res_lit_sel                           adaptive
% 19.85/2.99  --res_lit_sel_side                      none
% 19.85/2.99  --res_ordering                          kbo
% 19.85/2.99  --res_to_prop_solver                    active
% 19.85/2.99  --res_prop_simpl_new                    false
% 19.85/2.99  --res_prop_simpl_given                  true
% 19.85/2.99  --res_passive_queue_type                priority_queues
% 19.85/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.85/2.99  --res_passive_queues_freq               [15;5]
% 19.85/2.99  --res_forward_subs                      full
% 19.85/2.99  --res_backward_subs                     full
% 19.85/2.99  --res_forward_subs_resolution           true
% 19.85/2.99  --res_backward_subs_resolution          true
% 19.85/2.99  --res_orphan_elimination                true
% 19.85/2.99  --res_time_limit                        2.
% 19.85/2.99  --res_out_proof                         true
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Options
% 19.85/2.99  
% 19.85/2.99  --superposition_flag                    true
% 19.85/2.99  --sup_passive_queue_type                priority_queues
% 19.85/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.85/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.85/2.99  --demod_completeness_check              fast
% 19.85/2.99  --demod_use_ground                      true
% 19.85/2.99  --sup_to_prop_solver                    passive
% 19.85/2.99  --sup_prop_simpl_new                    true
% 19.85/2.99  --sup_prop_simpl_given                  true
% 19.85/2.99  --sup_fun_splitting                     true
% 19.85/2.99  --sup_smt_interval                      50000
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Simplification Setup
% 19.85/2.99  
% 19.85/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.85/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.85/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.85/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.85/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.85/2.99  --sup_immed_triv                        [TrivRules]
% 19.85/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_immed_bw_main                     []
% 19.85/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.85/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.85/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_input_bw                          []
% 19.85/2.99  
% 19.85/2.99  ------ Combination Options
% 19.85/2.99  
% 19.85/2.99  --comb_res_mult                         3
% 19.85/2.99  --comb_sup_mult                         2
% 19.85/2.99  --comb_inst_mult                        10
% 19.85/2.99  
% 19.85/2.99  ------ Debug Options
% 19.85/2.99  
% 19.85/2.99  --dbg_backtrace                         false
% 19.85/2.99  --dbg_dump_prop_clauses                 false
% 19.85/2.99  --dbg_dump_prop_clauses_file            -
% 19.85/2.99  --dbg_out_stat                          false
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  ------ Proving...
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  % SZS status Theorem for theBenchmark.p
% 19.85/2.99  
% 19.85/2.99   Resolution empty clause
% 19.85/2.99  
% 19.85/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.85/2.99  
% 19.85/2.99  fof(f16,conjecture,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f17,negated_conjecture,(
% 19.85/2.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 19.85/2.99    inference(negated_conjecture,[],[f16])).
% 19.85/2.99  
% 19.85/2.99  fof(f41,plain,(
% 19.85/2.99    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f17])).
% 19.85/2.99  
% 19.85/2.99  fof(f42,plain,(
% 19.85/2.99    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f41])).
% 19.85/2.99  
% 19.85/2.99  fof(f62,plain,(
% 19.85/2.99    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.85/2.99    inference(nnf_transformation,[],[f42])).
% 19.85/2.99  
% 19.85/2.99  fof(f63,plain,(
% 19.85/2.99    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f62])).
% 19.85/2.99  
% 19.85/2.99  fof(f64,plain,(
% 19.85/2.99    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.85/2.99    inference(rectify,[],[f63])).
% 19.85/2.99  
% 19.85/2.99  fof(f67,plain,(
% 19.85/2.99    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK9(X3),X0) & m2_yellow_6(sK9(X3),X0,X3)))) )),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f66,plain,(
% 19.85/2.99    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK8)) & l1_waybel_0(sK8,X0) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8))) )),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f65,plain,(
% 19.85/2.99    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,X1)) & l1_waybel_0(X1,sK7) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK7)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK7) & m2_yellow_6(X4,sK7,X3)) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7))),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f68,plain,(
% 19.85/2.99    ((! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,sK8)) & l1_waybel_0(sK8,sK7) & v7_waybel_0(sK8) & v4_orders_2(sK8) & ~v2_struct_0(sK8)) | ~v1_compts_1(sK7)) & (! [X3] : ((v3_yellow_6(sK9(X3),sK7) & m2_yellow_6(sK9(X3),sK7,X3)) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK7)) & l1_pre_topc(sK7) & v2_pre_topc(sK7) & ~v2_struct_0(sK7)),
% 19.85/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f64,f67,f66,f65])).
% 19.85/2.99  
% 19.85/2.99  fof(f107,plain,(
% 19.85/2.99    ( ! [X3] : (m2_yellow_6(sK9(X3),sK7,X3) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK7)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f68])).
% 19.85/2.99  
% 19.85/2.99  fof(f7,axiom,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f23,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f7])).
% 19.85/2.99  
% 19.85/2.99  fof(f24,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f23])).
% 19.85/2.99  
% 19.85/2.99  fof(f48,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(nnf_transformation,[],[f24])).
% 19.85/2.99  
% 19.85/2.99  fof(f49,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f48])).
% 19.85/2.99  
% 19.85/2.99  fof(f50,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(rectify,[],[f49])).
% 19.85/2.99  
% 19.85/2.99  fof(f53,plain,(
% 19.85/2.99    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6)))),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f52,plain,(
% 19.85/2.99    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,X3)))) )),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f51,plain,(
% 19.85/2.99    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f54,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK2(X0,X1,X2)) & m1_connsp_2(sK2(X0,X1,X2),X0,sK1(X0,X1,X2))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2))) | r2_hidden(sK1(X0,X1,X2),X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) & m1_connsp_2(sK3(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f50,f53,f52,f51])).
% 19.85/2.99  
% 19.85/2.99  fof(f81,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f54])).
% 19.85/2.99  
% 19.85/2.99  fof(f105,plain,(
% 19.85/2.99    v2_pre_topc(sK7)),
% 19.85/2.99    inference(cnf_transformation,[],[f68])).
% 19.85/2.99  
% 19.85/2.99  fof(f104,plain,(
% 19.85/2.99    ~v2_struct_0(sK7)),
% 19.85/2.99    inference(cnf_transformation,[],[f68])).
% 19.85/2.99  
% 19.85/2.99  fof(f106,plain,(
% 19.85/2.99    l1_pre_topc(sK7)),
% 19.85/2.99    inference(cnf_transformation,[],[f68])).
% 19.85/2.99  
% 19.85/2.99  fof(f8,axiom,(
% 19.85/2.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f25,plain,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f8])).
% 19.85/2.99  
% 19.85/2.99  fof(f26,plain,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f25])).
% 19.85/2.99  
% 19.85/2.99  fof(f85,plain,(
% 19.85/2.99    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f79,plain,(
% 19.85/2.99    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK3(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f54])).
% 19.85/2.99  
% 19.85/2.99  fof(f115,plain,(
% 19.85/2.99    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK3(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(equality_resolution,[],[f79])).
% 19.85/2.99  
% 19.85/2.99  fof(f82,plain,(
% 19.85/2.99    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK1(X0,X1,X2)) | r2_hidden(sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f54])).
% 19.85/2.99  
% 19.85/2.99  fof(f11,axiom,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f31,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f11])).
% 19.85/2.99  
% 19.85/2.99  fof(f32,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f31])).
% 19.85/2.99  
% 19.85/2.99  fof(f92,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f32])).
% 19.85/2.99  
% 19.85/2.99  fof(f4,axiom,(
% 19.85/2.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f19,plain,(
% 19.85/2.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 19.85/2.99    inference(ennf_transformation,[],[f4])).
% 19.85/2.99  
% 19.85/2.99  fof(f20,plain,(
% 19.85/2.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.85/2.99    inference(flattening,[],[f19])).
% 19.85/2.99  
% 19.85/2.99  fof(f75,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f20])).
% 19.85/2.99  
% 19.85/2.99  fof(f12,axiom,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f33,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f12])).
% 19.85/2.99  
% 19.85/2.99  fof(f34,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f33])).
% 19.85/2.99  
% 19.85/2.99  fof(f93,plain,(
% 19.85/2.99    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f34])).
% 19.85/2.99  
% 19.85/2.99  fof(f80,plain,(
% 19.85/2.99    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f54])).
% 19.85/2.99  
% 19.85/2.99  fof(f114,plain,(
% 19.85/2.99    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK3(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(equality_resolution,[],[f80])).
% 19.85/2.99  
% 19.85/2.99  fof(f15,axiom,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0)))) => v1_compts_1(X0)))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f39,plain,(
% 19.85/2.99    ! [X0] : ((v1_compts_1(X0) | ? [X1] : ((! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0))) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f15])).
% 19.85/2.99  
% 19.85/2.99  fof(f40,plain,(
% 19.85/2.99    ! [X0] : (v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f39])).
% 19.85/2.99  
% 19.85/2.99  fof(f60,plain,(
% 19.85/2.99    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK6(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK6(X0),k6_yellow_6(X0)) & l1_waybel_0(sK6(X0),X0) & v7_waybel_0(sK6(X0)) & v4_orders_2(sK6(X0)) & ~v2_struct_0(sK6(X0))))),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f61,plain,(
% 19.85/2.99    ! [X0] : (v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK6(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK6(X0),k6_yellow_6(X0)) & l1_waybel_0(sK6(X0),X0) & v7_waybel_0(sK6(X0)) & v4_orders_2(sK6(X0)) & ~v2_struct_0(sK6(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f60])).
% 19.85/2.99  
% 19.85/2.99  fof(f103,plain,(
% 19.85/2.99    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK6(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f61])).
% 19.85/2.99  
% 19.85/2.99  fof(f98,plain,(
% 19.85/2.99    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK6(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f61])).
% 19.85/2.99  
% 19.85/2.99  fof(f99,plain,(
% 19.85/2.99    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK6(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f61])).
% 19.85/2.99  
% 19.85/2.99  fof(f100,plain,(
% 19.85/2.99    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK6(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f61])).
% 19.85/2.99  
% 19.85/2.99  fof(f101,plain,(
% 19.85/2.99    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK6(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f61])).
% 19.85/2.99  
% 19.85/2.99  fof(f1,axiom,(
% 19.85/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f18,plain,(
% 19.85/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f1])).
% 19.85/2.99  
% 19.85/2.99  fof(f43,plain,(
% 19.85/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.85/2.99    inference(nnf_transformation,[],[f18])).
% 19.85/2.99  
% 19.85/2.99  fof(f44,plain,(
% 19.85/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.85/2.99    inference(rectify,[],[f43])).
% 19.85/2.99  
% 19.85/2.99  fof(f45,plain,(
% 19.85/2.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f46,plain,(
% 19.85/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.85/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 19.85/2.99  
% 19.85/2.99  fof(f70,plain,(
% 19.85/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f46])).
% 19.85/2.99  
% 19.85/2.99  fof(f3,axiom,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f47,plain,(
% 19.85/2.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.85/2.99    inference(nnf_transformation,[],[f3])).
% 19.85/2.99  
% 19.85/2.99  fof(f74,plain,(
% 19.85/2.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f47])).
% 19.85/2.99  
% 19.85/2.99  fof(f5,axiom,(
% 19.85/2.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f21,plain,(
% 19.85/2.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 19.85/2.99    inference(ennf_transformation,[],[f5])).
% 19.85/2.99  
% 19.85/2.99  fof(f76,plain,(
% 19.85/2.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f21])).
% 19.85/2.99  
% 19.85/2.99  fof(f6,axiom,(
% 19.85/2.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f22,plain,(
% 19.85/2.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(ennf_transformation,[],[f6])).
% 19.85/2.99  
% 19.85/2.99  fof(f77,plain,(
% 19.85/2.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f22])).
% 19.85/2.99  
% 19.85/2.99  fof(f9,axiom,(
% 19.85/2.99    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f27,plain,(
% 19.85/2.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f9])).
% 19.85/2.99  
% 19.85/2.99  fof(f28,plain,(
% 19.85/2.99    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f27])).
% 19.85/2.99  
% 19.85/2.99  fof(f89,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f28])).
% 19.85/2.99  
% 19.85/2.99  fof(f88,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f28])).
% 19.85/2.99  
% 19.85/2.99  fof(f87,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f28])).
% 19.85/2.99  
% 19.85/2.99  fof(f86,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f28])).
% 19.85/2.99  
% 19.85/2.99  fof(f10,axiom,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 19.85/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f29,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f10])).
% 19.85/2.99  
% 19.85/2.99  fof(f30,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f29])).
% 19.85/2.99  
% 19.85/2.99  fof(f55,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(nnf_transformation,[],[f30])).
% 19.85/2.99  
% 19.85/2.99  fof(f90,plain,(
% 19.85/2.99    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f55])).
% 19.85/3.00  
% 19.85/3.00  fof(f108,plain,(
% 19.85/3.00    ( ! [X3] : (v3_yellow_6(sK9(X3),sK7) | ~l1_waybel_0(X3,sK7) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK7)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f68])).
% 19.85/3.00  
% 19.85/3.00  fof(f2,axiom,(
% 19.85/3.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.85/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/3.00  
% 19.85/3.00  fof(f72,plain,(
% 19.85/3.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f2])).
% 19.85/3.00  
% 19.85/3.00  fof(f69,plain,(
% 19.85/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f46])).
% 19.85/3.00  
% 19.85/3.00  fof(f14,axiom,(
% 19.85/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 19.85/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/3.00  
% 19.85/3.00  fof(f37,plain,(
% 19.85/3.00    ! [X0] : ((! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~v1_compts_1(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/3.00    inference(ennf_transformation,[],[f14])).
% 19.85/3.00  
% 19.85/3.00  fof(f38,plain,(
% 19.85/3.00    ! [X0] : (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/3.00    inference(flattening,[],[f37])).
% 19.85/3.00  
% 19.85/3.00  fof(f58,plain,(
% 19.85/3.00    ! [X1,X0] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r3_waybel_9(X0,X1,sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 19.85/3.00    introduced(choice_axiom,[])).
% 19.85/3.00  
% 19.85/3.00  fof(f59,plain,(
% 19.85/3.00    ! [X0] : (! [X1] : ((r3_waybel_9(X0,X1,sK5(X0,X1)) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f58])).
% 19.85/3.00  
% 19.85/3.00  fof(f97,plain,(
% 19.85/3.00    ( ! [X0,X1] : (r3_waybel_9(X0,X1,sK5(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f59])).
% 19.85/3.00  
% 19.85/3.00  fof(f13,axiom,(
% 19.85/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 19.85/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.85/3.00  
% 19.85/3.00  fof(f35,plain,(
% 19.85/3.00    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/3.00    inference(ennf_transformation,[],[f13])).
% 19.85/3.00  
% 19.85/3.00  fof(f36,plain,(
% 19.85/3.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/3.00    inference(flattening,[],[f35])).
% 19.85/3.00  
% 19.85/3.00  fof(f56,plain,(
% 19.85/3.00    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2))) & m2_yellow_6(sK4(X0,X1,X2),X0,X1)))),
% 19.85/3.00    introduced(choice_axiom,[])).
% 19.85/3.00  
% 19.85/3.00  fof(f57,plain,(
% 19.85/3.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2))) & m2_yellow_6(sK4(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f56])).
% 19.85/3.00  
% 19.85/3.00  fof(f94,plain,(
% 19.85/3.00    ( ! [X2,X0,X1] : (m2_yellow_6(sK4(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f57])).
% 19.85/3.00  
% 19.85/3.00  fof(f91,plain,(
% 19.85/3.00    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f55])).
% 19.85/3.00  
% 19.85/3.00  fof(f113,plain,(
% 19.85/3.00    ( ! [X2] : (~v3_yellow_6(X2,sK7) | ~m2_yellow_6(X2,sK7,sK8) | ~v1_compts_1(sK7)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f68])).
% 19.85/3.00  
% 19.85/3.00  fof(f109,plain,(
% 19.85/3.00    ~v2_struct_0(sK8) | ~v1_compts_1(sK7)),
% 19.85/3.00    inference(cnf_transformation,[],[f68])).
% 19.85/3.00  
% 19.85/3.00  fof(f110,plain,(
% 19.85/3.00    v4_orders_2(sK8) | ~v1_compts_1(sK7)),
% 19.85/3.00    inference(cnf_transformation,[],[f68])).
% 19.85/3.00  
% 19.85/3.00  fof(f111,plain,(
% 19.85/3.00    v7_waybel_0(sK8) | ~v1_compts_1(sK7)),
% 19.85/3.00    inference(cnf_transformation,[],[f68])).
% 19.85/3.00  
% 19.85/3.00  fof(f112,plain,(
% 19.85/3.00    l1_waybel_0(sK8,sK7) | ~v1_compts_1(sK7)),
% 19.85/3.00    inference(cnf_transformation,[],[f68])).
% 19.85/3.00  
% 19.85/3.00  fof(f96,plain,(
% 19.85/3.00    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f59])).
% 19.85/3.00  
% 19.85/3.00  fof(f95,plain,(
% 19.85/3.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/3.00    inference(cnf_transformation,[],[f57])).
% 19.85/3.00  
% 19.85/3.00  fof(f73,plain,(
% 19.85/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.85/3.00    inference(cnf_transformation,[],[f47])).
% 19.85/3.00  
% 19.85/3.00  cnf(c_41,negated_conjecture,
% 19.85/3.00      ( m2_yellow_6(sK9(X0),sK7,X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f107]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7863,plain,
% 19.85/3.00      ( m2_yellow_6(sK9(X0),sK7,X0) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | m1_subset_1(sK1(X1,X0,X2),u1_struct_0(X1))
% 19.85/3.00      | ~ v2_pre_topc(X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k10_yellow_6(X1,X0) = X2 ),
% 19.85/3.00      inference(cnf_transformation,[],[f81]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_43,negated_conjecture,
% 19.85/3.00      ( v2_pre_topc(sK7) ),
% 19.85/3.00      inference(cnf_transformation,[],[f105]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1926,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | m1_subset_1(sK1(X1,X0,X2),u1_struct_0(X1))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k10_yellow_6(X1,X0) = X2
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_12,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1927,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = X1 ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1926]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_44,negated_conjecture,
% 19.85/3.00      ( ~ v2_struct_0(sK7) ),
% 19.85/3.00      inference(cnf_transformation,[],[f104]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_42,negated_conjecture,
% 19.85/3.00      ( l1_pre_topc(sK7) ),
% 19.85/3.00      inference(cnf_transformation,[],[f106]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1931,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = X1 ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1927,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1932,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = X1 ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1931]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7842,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = X1
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | ~ v2_pre_topc(X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f85]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1851,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_16,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1852,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1851]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1856,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1852,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1857,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1856]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/3.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f115]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1677,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/3.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_14,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1678,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1677]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1682,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1678,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1683,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1682]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1874,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_1857,c_1683]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7845,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(sK7,X0,X1),sK7,X1) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1874]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11,plain,
% 19.85/3.00      ( ~ m1_connsp_2(X0,X1,sK1(X1,X2,X3))
% 19.85/3.00      | r1_waybel_0(X1,X2,X0)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | r2_hidden(sK1(X1,X2,X3),X3)
% 19.85/3.00      | ~ v2_pre_topc(X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k10_yellow_6(X1,X2) = X3 ),
% 19.85/3.00      inference(cnf_transformation,[],[f82]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1959,plain,
% 19.85/3.00      ( ~ m1_connsp_2(X0,X1,sK1(X1,X2,X3))
% 19.85/3.00      | r1_waybel_0(X1,X2,X0)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/3.00      | r2_hidden(sK1(X1,X2,X3),X3)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k10_yellow_6(X1,X2) = X3
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_11,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1960,plain,
% 19.85/3.00      ( ~ m1_connsp_2(X0,sK7,sK1(sK7,X1,X2))
% 19.85/3.00      | r1_waybel_0(sK7,X1,X0)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,X2),X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(sK7)
% 19.85/3.00      | k10_yellow_6(sK7,X1) = X2 ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1959]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1964,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ m1_connsp_2(X0,sK7,sK1(sK7,X1,X2))
% 19.85/3.00      | r1_waybel_0(sK7,X1,X0)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,X2),X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | k10_yellow_6(sK7,X1) = X2 ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1960,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1965,plain,
% 19.85/3.00      ( ~ m1_connsp_2(X0,sK7,sK1(sK7,X1,X2))
% 19.85/3.00      | r1_waybel_0(sK7,X1,X0)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,X2),X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | k10_yellow_6(sK7,X1) = X2 ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1964]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7841,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = X1
% 19.85/3.00      | m1_connsp_2(X2,sK7,sK1(sK7,X0,X1)) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X0,X2) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1965]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10727,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = X1
% 19.85/3.00      | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,X1),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7845,c_7841]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2472,plain,
% 19.85/3.00      ( r1_waybel_0(sK7,X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X2,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X3,u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(X3,k10_yellow_6(sK7,X2))
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X4),X4)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | sK3(sK7,X2,X3) != X1
% 19.85/3.00      | sK1(sK7,X0,X4) != X3
% 19.85/3.00      | k10_yellow_6(sK7,X0) = X4
% 19.85/3.00      | sK7 != sK7 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_1874,c_1965]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2473,plain,
% 19.85/3.00      ( r1_waybel_0(sK7,X0,sK3(sK7,X1,sK1(sK7,X0,X2)))
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,X0,X2),u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X2),X2)
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X2),k10_yellow_6(sK7,X1))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = X2 ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2472]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2505,plain,
% 19.85/3.00      ( r1_waybel_0(sK7,X0,sK3(sK7,X1,sK1(sK7,X0,X2)))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X2),X2)
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X2),k10_yellow_6(sK7,X1))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = X2 ),
% 19.85/3.00      inference(forward_subsumption_resolution,[status(thm)],[c_2473,c_1932]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2519,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = X1
% 19.85/3.00      | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2505]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12687,plain,
% 19.85/3.00      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,X0) = X1
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_10727,c_2519]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12688,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = X1
% 19.85/3.00      | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,X1))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),X1) = iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,X1),k10_yellow_6(sK7,X2)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_12687]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_23,plain,
% 19.85/3.00      ( r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f92]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1644,plain,
% 19.85/3.00      ( r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_23,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1645,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1644]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1649,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1645,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1650,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1649]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7850,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1651,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7846,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1857]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_6,plain,
% 19.85/3.00      ( m1_subset_1(X0,X1)
% 19.85/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.85/3.00      | ~ r2_hidden(X0,X2) ),
% 19.85/3.00      inference(cnf_transformation,[],[f75]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7869,plain,
% 19.85/3.00      ( m1_subset_1(X0,X1) = iProver_top
% 19.85/3.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 19.85/3.00      | r2_hidden(X0,X2) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8666,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) = iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7846,c_7869]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9100,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X0,X1) = iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_7850,c_1651,c_8666]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9101,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0)) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_9100]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12695,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X0,sK3(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1)))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,k10_yellow_6(sK7,X1)),k10_yellow_6(sK7,X2)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_12688,c_9101]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | r3_waybel_9(X0,X3,X2)
% 19.85/3.00      | ~ m2_yellow_6(X1,X0,X3)
% 19.85/3.00      | ~ l1_waybel_0(X3,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X3)
% 19.85/3.00      | ~ v4_orders_2(X3)
% 19.85/3.00      | ~ v7_waybel_0(X3)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f93]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1612,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | r3_waybel_9(X0,X3,X2)
% 19.85/3.00      | ~ m2_yellow_6(X1,X0,X3)
% 19.85/3.00      | ~ l1_waybel_0(X3,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X3)
% 19.85/3.00      | ~ v4_orders_2(X3)
% 19.85/3.00      | ~ v7_waybel_0(X3)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_24,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1613,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,X1)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1612]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1615,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,X1)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X2) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1613,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1616,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,X1)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1615]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7851,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X2,X1) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_13099,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,X2) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X0,sK3(sK7,X3,sK1(sK7,X0,k10_yellow_6(sK7,X1)))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X3,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,k10_yellow_6(sK7,X1)),k10_yellow_6(sK7,X3)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X3) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(X3) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X3) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_12695,c_7851]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_13596,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,X3) != iProver_top
% 19.85/3.00      | m2_yellow_6(X3,sK7,X2) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X0,sK3(sK7,X4,sK1(sK7,X0,k10_yellow_6(sK7,X1)))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X3,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X4,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X0,k10_yellow_6(sK7,X1)),k10_yellow_6(sK7,X4)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X4) = iProver_top
% 19.85/3.00      | v2_struct_0(X3) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X4) != iProver_top
% 19.85/3.00      | v4_orders_2(X3) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X4) != iProver_top
% 19.85/3.00      | v7_waybel_0(X3) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_13099,c_7851]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_13767,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X1,sK3(sK7,X3,sK1(sK7,X1,k10_yellow_6(sK7,X0)))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X3,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X3)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X3) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X3) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X3) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_13596]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1858,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1857]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_13776,plain,
% 19.85/3.00      ( m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X3,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X1,sK3(sK7,X3,sK1(sK7,X1,k10_yellow_6(sK7,X0)))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X3)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X3) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X3) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X3) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_13767,c_1858]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_13777,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,X1,sK3(sK7,X3,sK1(sK7,X1,k10_yellow_6(sK7,X0)))) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X3,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X3)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X3) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X3) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X3) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_13776]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_13,plain,
% 19.85/3.00      ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/3.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f114]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1713,plain,
% 19.85/3.00      ( ~ r1_waybel_0(X0,X1,sK3(X0,X1,X2))
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 19.85/3.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_13,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1714,plain,
% 19.85/3.00      ( ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1713]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1718,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1714,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1719,plain,
% 19.85/3.00      ( ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1718]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1875,plain,
% 19.85/3.00      ( ~ r1_waybel_0(sK7,X0,sK3(sK7,X0,X1))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_1857,c_1719]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7844,plain,
% 19.85/3.00      ( r1_waybel_0(sK7,X0,sK3(sK7,X0,X1)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,X0)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1875]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_13782,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_13777,c_7844]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14281,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_13782,c_9101]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_27866,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X0,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7842,c_14281]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,sK6(X0),X1)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.85/3.00      | v1_compts_1(X0)
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f103]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1495,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,sK6(X0),X1)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 19.85/3.00      | v1_compts_1(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_29,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1496,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,sK6(sK7),X0)
% 19.85/3.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1495]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1500,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,sK6(sK7),X0)
% 19.85/3.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 19.85/3.00      | v1_compts_1(sK7) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1496,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7855,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK6(sK7),X0) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1500]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_27889,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X1),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X1)) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X1)) != iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X1)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_27866,c_7855]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_34,plain,
% 19.85/3.00      ( v1_compts_1(X0)
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v2_struct_0(sK6(X0))
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f98]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1425,plain,
% 19.85/3.00      ( v1_compts_1(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v2_struct_0(sK6(X0))
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_34,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1426,plain,
% 19.85/3.00      ( v1_compts_1(sK7)
% 19.85/3.00      | ~ v2_struct_0(sK6(sK7))
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1425]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1428,plain,
% 19.85/3.00      ( v1_compts_1(sK7) | ~ v2_struct_0(sK6(sK7)) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1426,c_44,c_43,c_42,c_62]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1430,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top | v2_struct_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_33,plain,
% 19.85/3.00      ( v1_compts_1(X0)
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v4_orders_2(sK6(X0))
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f99]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1439,plain,
% 19.85/3.00      ( v1_compts_1(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v4_orders_2(sK6(X0))
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_33,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1440,plain,
% 19.85/3.00      ( v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1439]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1442,plain,
% 19.85/3.00      ( v4_orders_2(sK6(sK7)) | v1_compts_1(sK7) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1440,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1443,plain,
% 19.85/3.00      ( v1_compts_1(sK7) | v4_orders_2(sK6(sK7)) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1442]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1444,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top | v4_orders_2(sK6(sK7)) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1443]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_32,plain,
% 19.85/3.00      ( v1_compts_1(X0)
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v7_waybel_0(sK6(X0))
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f100]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1453,plain,
% 19.85/3.00      ( v1_compts_1(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v7_waybel_0(sK6(X0))
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_32,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1454,plain,
% 19.85/3.00      ( v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | v7_waybel_0(sK6(sK7))
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1453]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1456,plain,
% 19.85/3.00      ( v7_waybel_0(sK6(sK7)) | v1_compts_1(sK7) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1454,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1457,plain,
% 19.85/3.00      ( v1_compts_1(sK7) | v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1456]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1458,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top | v7_waybel_0(sK6(sK7)) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_31,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(X0),X0)
% 19.85/3.00      | v1_compts_1(X0)
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f101]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1467,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(X0),X0)
% 19.85/3.00      | v1_compts_1(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_31,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1468,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1467]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1470,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(sK7),sK7) | v1_compts_1(sK7) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1468,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1472,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(sK7),sK7) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1,plain,
% 19.85/3.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7874,plain,
% 19.85/3.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.85/3.00      | r1_tarski(X0,X1) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_4,plain,
% 19.85/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f74]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7871,plain,
% 19.85/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 19.85/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8665,plain,
% 19.85/3.00      ( m1_subset_1(X0,X1) = iProver_top
% 19.85/3.00      | r2_hidden(X0,X2) != iProver_top
% 19.85/3.00      | r1_tarski(X2,X1) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7871,c_7869]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9698,plain,
% 19.85/3.00      ( m1_subset_1(sK0(X0,X1),X2) = iProver_top
% 19.85/3.00      | r1_tarski(X0,X2) != iProver_top
% 19.85/3.00      | r1_tarski(X0,X1) = iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7874,c_8665]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9106,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,sK0(k10_yellow_6(sK7,X0),X1)) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,X0),X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7874,c_9101]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10038,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK0(k10_yellow_6(sK7,sK6(sK7)),X0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_9106,c_7855]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10968,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
% 19.85/3.00      | m1_subset_1(sK0(k10_yellow_6(sK7,sK6(sK7)),X0),u1_struct_0(sK7)) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_10038,c_1430,c_1444,c_1458,c_1472]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10969,plain,
% 19.85/3.00      ( m1_subset_1(sK0(k10_yellow_6(sK7,sK6(sK7)),X0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_10968]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10974,plain,
% 19.85/3.00      ( r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_9698,c_10969]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10030,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK0(k10_yellow_6(sK7,X0),X1),u1_struct_0(sK7)) = iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,X0),X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7874,c_8666]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11738,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_10030,c_10969]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_18950,plain,
% 19.85/3.00      ( r1_tarski(k10_yellow_6(sK7,sK6(sK7)),X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_10974,c_1430,c_1444,c_1458,c_1472,c_11738]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7,plain,
% 19.85/3.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f76]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7868,plain,
% 19.85/3.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14278,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,X1),sK1(sK7,X1,k10_yellow_6(sK7,X0))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_13782,c_7868]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_28298,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X1),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X1)) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X1)) != iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X1)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_18950,c_14278]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29103,plain,
% 19.85/3.00      ( v7_waybel_0(sK9(X1)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X1)) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X1),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X1)) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_27889,c_1430,c_1444,c_1458,c_1472,c_28298]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29104,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X1),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X1)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X1)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X1)) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_29103]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29109,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X1),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X1)) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X1)) != iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X1)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7842,c_29104]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29117,plain,
% 19.85/3.00      ( v7_waybel_0(sK9(X1)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X1)) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X1),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X1)) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_29109,c_1430,c_1444,c_1458,c_1472,c_1858]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29118,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X1)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X1),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X1)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X1)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X1)) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_29117]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29127,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_29118,c_7851]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_29142,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X0),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7842,c_29127]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_40041,plain,
% 19.85/3.00      ( v7_waybel_0(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_29142,c_1430,c_1444,c_1458,c_1472,c_1858]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_40042,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK6(sK7)) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(X2)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X2),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X2)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X2)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X2)) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_40041]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_40047,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X0),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X0)) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK9(X0))) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X0)) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK9(X0))) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X0)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK9(X0))) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_40042]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8,plain,
% 19.85/3.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f77]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | l1_waybel_0(X0,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_struct_0(X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f89]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_841,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | l1_waybel_0(X0,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X3)
% 19.85/3.00      | X1 != X3 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_842,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | l1_waybel_0(X0,X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X1) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_841]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2131,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | l1_waybel_0(X0,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_842,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2132,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | l1_waybel_0(X0,sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2131]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2134,plain,
% 19.85/3.00      ( v2_struct_0(X1)
% 19.85/3.00      | l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(global_propositional_subsumption,[status(thm)],[c_2132,c_44]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2135,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | l1_waybel_0(X0,sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_2134]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2136,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2135]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_18,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_struct_0(X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f88]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_813,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X3)
% 19.85/3.00      | X1 != X3 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_814,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_813]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2157,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | v7_waybel_0(X0)
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_814,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2158,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | v7_waybel_0(X0) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2157]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2160,plain,
% 19.85/3.00      ( v2_struct_0(X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | v7_waybel_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,[status(thm)],[c_2158,c_44]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2161,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_2160]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2162,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_19,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_struct_0(X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f87]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_785,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X3)
% 19.85/3.00      | X1 != X3 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_786,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X1) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_785]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2183,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_786,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2184,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2183]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2186,plain,
% 19.85/3.00      ( v2_struct_0(X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(global_propositional_subsumption,[status(thm)],[c_2184,c_44]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2187,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_2186]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2188,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) = iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2187]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_20,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | ~ v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_struct_0(X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f86]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_757,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | ~ v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X3)
% 19.85/3.00      | X1 != X3 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_758,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | ~ v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ l1_pre_topc(X1) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_757]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2209,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X2,X1)
% 19.85/3.00      | ~ v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_758,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2210,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2209]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2212,plain,
% 19.85/3.00      ( v2_struct_0(X1)
% 19.85/3.00      | ~ v2_struct_0(X0)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(global_propositional_subsumption,[status(thm)],[c_2210,c_44]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2213,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | ~ v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_2212]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2214,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) != iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2692,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | ~ v2_struct_0(X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | X0 != X1
% 19.85/3.00      | sK9(X1) != X2
% 19.85/3.00      | sK7 != sK7 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_41,c_2213]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2693,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v2_struct_0(sK9(X0))
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2692]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2694,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X0)) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2693]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2716,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | v4_orders_2(X2)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | X0 != X1
% 19.85/3.00      | sK9(X1) != X2
% 19.85/3.00      | sK7 != sK7 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_41,c_2187]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2717,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | v4_orders_2(sK9(X0))
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2716]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2718,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X0)) = iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2717]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2740,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | v7_waybel_0(X2)
% 19.85/3.00      | X0 != X1
% 19.85/3.00      | sK9(X1) != X2
% 19.85/3.00      | sK7 != sK7 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_41,c_2161]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2741,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | v7_waybel_0(sK9(X0)) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2740]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2742,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X0)) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2741]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2764,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(X1,sK7)
% 19.85/3.00      | l1_waybel_0(X2,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | X0 != X1
% 19.85/3.00      | sK9(X1) != X2
% 19.85/3.00      | sK7 != sK7 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_41,c_2135]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2765,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | l1_waybel_0(sK9(X0),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_2764]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2766,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X0),sK7) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2765]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7840,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2135]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8820,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(X0),sK7) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_7840]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7839,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8581,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X0)) = iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_7839]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8823,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X0)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X0)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X0)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK9(X0))) = iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_8820,c_8581]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10979,plain,
% 19.85/3.00      ( v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK9(X0))) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_8823,c_2694,c_2718,c_2742]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10980,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK9(X0))) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_10979]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7838,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) = iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2187]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8578,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X0)) = iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_7838]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8824,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X0)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X0)) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK9(X0))) = iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X0)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_8820,c_8578]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11007,plain,
% 19.85/3.00      ( v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK9(X0))) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_8824,c_2694,c_2718,c_2742]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11008,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK9(X0))) = iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_11007]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7837,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) != iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8250,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X0)) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_7837]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8825,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(X0)) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK9(X0))) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(X0)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(X0)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_8820,c_8250]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11409,plain,
% 19.85/3.00      ( v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK9(X0))) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_8825,c_2694,c_2718,c_2742]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11410,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK9(X0))) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_11409]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_40056,plain,
% 19.85/3.00      ( v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_40047,c_2136,c_2162,c_2188,c_2214,c_2694,c_2718,c_2742,
% 19.85/3.00                 c_2766,c_10980,c_11008,c_11410]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_40057,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_40056]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_40064,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0)))),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_40057,c_7851]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_42914,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(X0))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7842,c_40064]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_42929,plain,
% 19.85/3.00      ( v7_waybel_0(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(X0))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_42914,c_1430,c_1444,c_1458,c_1472]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_42930,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(X0))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(X0))))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 19.85/3.00      | m2_yellow_6(X2,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(X0)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(X0))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_42929]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_42933,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(sK9(X0)))) = k10_yellow_6(sK7,sK6(sK7))
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,sK6(sK7),k10_yellow_6(sK7,sK9(sK9(sK9(X0)))))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK9(sK9(X0))),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,sK9(sK9(sK9(X0)))),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_42930]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8180,plain,
% 19.85/3.00      ( m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7))
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_41]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8238,plain,
% 19.85/3.00      ( m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7)) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8180]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_22,plain,
% 19.85/3.00      ( ~ v3_yellow_6(X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | ~ v2_pre_topc(X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 19.85/3.00      inference(cnf_transformation,[],[f90]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_40,negated_conjecture,
% 19.85/3.00      ( v3_yellow_6(sK9(X0),sK7)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f108]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_939,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X2,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | ~ v2_pre_topc(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X2)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X2)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k10_yellow_6(X1,X0) != k1_xboole_0
% 19.85/3.00      | sK9(X2) != X0
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_22,c_40]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_940,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK9(X0),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | ~ v2_pre_topc(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK9(X0))
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(sK9(X0))
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(sK9(X0))
% 19.85/3.00      | ~ l1_pre_topc(sK7)
% 19.85/3.00      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_939]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_944,plain,
% 19.85/3.00      ( ~ v7_waybel_0(sK9(X0))
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(sK9(X0))
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK9(X0),sK7)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK9(X0))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_940,c_44,c_43,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_945,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK9(X0),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK9(X0))
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(sK9(X0))
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(sK9(X0))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_944]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2947,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK9(X0),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(sK9(X0))
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(sK9(X0))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 19.85/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_2693,c_945]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2958,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK9(X0),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(sK9(X0))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 19.85/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_2717,c_2947]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2969,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK9(X0),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 19.85/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_2741,c_2958]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2975,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,sK9(X0)) != k1_xboole_0 ),
% 19.85/3.00      inference(backward_subsumption_resolution,[status(thm)],[c_2765,c_2969]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8300,plain,
% 19.85/3.00      ( ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK6(sK7))) != k1_xboole_0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2975]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8301,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK6(sK7))) != k1_xboole_0
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8300]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8113,plain,
% 19.85/3.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | ~ r1_tarski(X0,u1_struct_0(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_4]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8437,plain,
% 19.85/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | ~ r1_tarski(k1_xboole_0,u1_struct_0(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_8113]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8438,plain,
% 19.85/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 19.85/3.00      | r1_tarski(k1_xboole_0,u1_struct_0(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8437]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_3,plain,
% 19.85/3.00      ( r1_tarski(k1_xboole_0,X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f72]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8573,plain,
% 19.85/3.00      ( r1_tarski(k1_xboole_0,u1_struct_0(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8574,plain,
% 19.85/3.00      ( r1_tarski(k1_xboole_0,u1_struct_0(sK7)) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8573]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8153,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK6(sK7))
% 19.85/3.00      | l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2135]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8599,plain,
% 19.85/3.00      ( ~ m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7))
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_8153]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8600,plain,
% 19.85/3.00      ( m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8599]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7857,plain,
% 19.85/3.00      ( l1_waybel_0(sK6(sK7),sK7) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8729,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7857,c_8578]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9868,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_8729,c_1430,c_1444,c_1458]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8733,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7857,c_8581]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9873,plain,
% 19.85/3.00      ( v7_waybel_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_8733,c_1430,c_1444,c_1458]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9874,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_9873]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9036,plain,
% 19.85/3.00      ( ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),X0),u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7)))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK6(sK7))) = X0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1932]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9946,plain,
% 19.85/3.00      ( ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7)))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_9036]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9966,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) = iProver_top
% 19.85/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_9946]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8420,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7857,c_8250]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9978,plain,
% 19.85/3.00      ( v2_struct_0(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_8420,c_1430,c_1444,c_1458]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9979,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_9978]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11583,plain,
% 19.85/3.00      ( r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_3]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11584,plain,
% 19.85/3.00      ( r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_11583]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9242,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK6(X0),X1)
% 19.85/3.00      | ~ l1_waybel_0(sK6(X0),sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | ~ r2_hidden(X1,k10_yellow_6(sK7,sK6(X0)))
% 19.85/3.00      | v2_struct_0(sK6(X0))
% 19.85/3.00      | ~ v4_orders_2(sK6(X0))
% 19.85/3.00      | ~ v7_waybel_0(sK6(X0)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1650]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12475,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK6(X0),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | ~ l1_waybel_0(sK6(X0),sK7)
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | ~ r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(X0)))
% 19.85/3.00      | v2_struct_0(sK6(X0))
% 19.85/3.00      | ~ v4_orders_2(sK6(X0))
% 19.85/3.00      | ~ v7_waybel_0(sK6(X0)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_9242]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12501,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK6(X0),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(X0),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(X0))) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(X0)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(X0)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(X0)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_12475]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12503,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(sK7))) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_12501]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12550,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | v1_compts_1(sK7) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1500]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12554,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_12550]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9037,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK9(sK6(sK7)),X0)
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 19.85/3.00      | ~ r2_hidden(X0,k10_yellow_6(sK7,sK9(sK6(sK7))))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1650]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12539,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | ~ r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7))))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_9037]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12576,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7)))) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_12539]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9030,plain,
% 19.85/3.00      ( ~ r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),X0))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(X0,k10_yellow_6(sK7,sK9(sK6(sK7))))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1875]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12537,plain,
% 19.85/3.00      ( ~ r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7))))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_9030]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12580,plain,
% 19.85/3.00      ( r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7)))) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_12537]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9031,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),X0),sK7,X0)
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(X0,u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(X0,k10_yellow_6(sK7,sK9(sK6(sK7))))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1874]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12536,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7))))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_9031]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12582,plain,
% 19.85/3.00      ( m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK9(sK6(sK7)))) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_12536]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8171,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | r3_waybel_9(sK7,sK6(sK7),X1)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,sK6(sK7))
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1616]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_12477,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,sK6(sK7))
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_8171]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_20404,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | ~ m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7))
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | ~ m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_12477]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_20405,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
% 19.85/3.00      | r3_waybel_9(sK7,sK6(sK7),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) = iProver_top
% 19.85/3.00      | m2_yellow_6(sK9(sK6(sK7)),sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_20404]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_2,plain,
% 19.85/3.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.85/3.00      inference(cnf_transformation,[],[f69]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8767,plain,
% 19.85/3.00      ( ~ r2_hidden(X0,X1)
% 19.85/3.00      | r2_hidden(X0,k10_yellow_6(sK7,sK6(sK7)))
% 19.85/3.00      | ~ r1_tarski(X1,k10_yellow_6(sK7,sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10153,plain,
% 19.85/3.00      ( r2_hidden(X0,k10_yellow_6(sK7,sK6(sK7)))
% 19.85/3.00      | ~ r2_hidden(X0,k1_xboole_0)
% 19.85/3.00      | ~ r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_8767]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_31642,plain,
% 19.85/3.00      ( r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(sK7)))
% 19.85/3.00      | ~ r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0)
% 19.85/3.00      | ~ r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_10153]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_31643,plain,
% 19.85/3.00      ( r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k10_yellow_6(sK7,sK6(sK7))) = iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0) != iProver_top
% 19.85/3.00      | r1_tarski(k1_xboole_0,k10_yellow_6(sK7,sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_31642]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8997,plain,
% 19.85/3.00      ( ~ m1_connsp_2(X0,sK7,sK1(sK7,sK9(sK6(sK7)),X1))
% 19.85/3.00      | r1_waybel_0(sK7,sK9(sK6(sK7)),X0)
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),X1),X1)
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7)))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK6(sK7))) = X1 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1965]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9916,plain,
% 19.85/3.00      ( ~ m1_connsp_2(X0,sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | r1_waybel_0(sK7,sK9(sK6(sK7)),X0)
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0)
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7)))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_8997]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_43239,plain,
% 19.85/3.00      ( ~ m1_connsp_2(sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))
% 19.85/3.00      | r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7)))
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0)
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7)))
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0 ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_9916]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_43242,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0
% 19.85/3.00      | m1_connsp_2(sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(X0)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_43239]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_43244,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK6(sK7))) = k1_xboole_0
% 19.85/3.00      | m1_connsp_2(sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)),sK7,sK1(sK7,sK9(sK6(sK7)),k1_xboole_0)) != iProver_top
% 19.85/3.00      | r1_waybel_0(sK7,sK9(sK6(sK7)),sK3(sK7,sK9(sK6(sK7)),sK1(sK7,sK9(sK6(sK7)),k1_xboole_0))) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,sK9(sK6(sK7)),k1_xboole_0),k1_xboole_0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_43242]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_44216,plain,
% 19.85/3.00      ( v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_42933,c_1430,c_1444,c_1458,c_1472,c_8238,c_8301,c_8438,
% 19.85/3.00                 c_8574,c_8600,c_9868,c_9874,c_9966,c_9979,c_11584,c_12503,
% 19.85/3.00                 c_12554,c_12576,c_12580,c_12582,c_20405,c_31643,c_43244]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_27,plain,
% 19.85/3.00      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ v1_compts_1(X0)
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f97]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1516,plain,
% 19.85/3.00      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ v1_compts_1(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_27,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1517,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1516]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1521,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1517,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1522,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,sK5(sK7,X0))
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1521]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7854,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,sK5(sK7,X0)) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_26,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | m2_yellow_6(sK4(X0,X1,X2),X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f94]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1546,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | m2_yellow_6(sK4(X0,X1,X2),X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_26,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1547,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1546]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1551,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1547,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1552,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1551]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7853,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 19.85/3.00      | m2_yellow_6(sK4(sK7,X0,X1),sK7,X0) = iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1552]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_21,plain,
% 19.85/3.00      ( v3_yellow_6(X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | ~ v2_pre_topc(X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 19.85/3.00      inference(cnf_transformation,[],[f91]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_35,negated_conjecture,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | ~ v3_yellow_6(X0,sK7)
% 19.85/3.00      | ~ v1_compts_1(sK7) ),
% 19.85/3.00      inference(cnf_transformation,[],[f113]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_906,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | ~ l1_waybel_0(X1,X2)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | ~ v2_pre_topc(X2)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X2)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X2)
% 19.85/3.00      | X0 != X1
% 19.85/3.00      | k10_yellow_6(X2,X1) = k1_xboole_0
% 19.85/3.00      | sK7 != X2 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_907,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | ~ v2_pre_topc(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_906]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_911,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_907,c_44,c_43,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_912,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k1_xboole_0 ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_911]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7861,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK8) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_45,plain,
% 19.85/3.00      ( v2_struct_0(sK7) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_46,plain,
% 19.85/3.00      ( v2_pre_topc(sK7) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_47,plain,
% 19.85/3.00      ( l1_pre_topc(sK7) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_39,negated_conjecture,
% 19.85/3.00      ( ~ v1_compts_1(sK7) | ~ v2_struct_0(sK8) ),
% 19.85/3.00      inference(cnf_transformation,[],[f109]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_54,plain,
% 19.85/3.00      ( v1_compts_1(sK7) != iProver_top | v2_struct_0(sK8) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_38,negated_conjecture,
% 19.85/3.00      ( ~ v1_compts_1(sK7) | v4_orders_2(sK8) ),
% 19.85/3.00      inference(cnf_transformation,[],[f110]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_55,plain,
% 19.85/3.00      ( v1_compts_1(sK7) != iProver_top | v4_orders_2(sK8) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_37,negated_conjecture,
% 19.85/3.00      ( ~ v1_compts_1(sK7) | v7_waybel_0(sK8) ),
% 19.85/3.00      inference(cnf_transformation,[],[f111]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_56,plain,
% 19.85/3.00      ( v1_compts_1(sK7) != iProver_top | v7_waybel_0(sK8) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_36,negated_conjecture,
% 19.85/3.00      ( l1_waybel_0(sK8,sK7) | ~ v1_compts_1(sK7) ),
% 19.85/3.00      inference(cnf_transformation,[],[f112]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_57,plain,
% 19.85/3.00      ( l1_waybel_0(sK8,sK7) = iProver_top | v1_compts_1(sK7) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_908,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK8) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_pre_topc(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK7) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | l1_pre_topc(sK7) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7970,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK8,sK7)
% 19.85/3.00      | v2_struct_0(sK8)
% 19.85/3.00      | ~ v4_orders_2(sK8)
% 19.85/3.00      | ~ v7_waybel_0(sK8) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2135]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7971,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_7970]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7975,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | ~ l1_waybel_0(sK8,sK7)
% 19.85/3.00      | v2_struct_0(sK8)
% 19.85/3.00      | ~ v4_orders_2(sK8)
% 19.85/3.00      | v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(sK8) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2161]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7976,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) = iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_7975]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7980,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK8)
% 19.85/3.00      | ~ l1_waybel_0(sK8,sK7)
% 19.85/3.00      | v2_struct_0(sK8)
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(sK8)
% 19.85/3.00      | ~ v7_waybel_0(sK8) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2187]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7981,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_7980]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9091,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK8) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k1_xboole_0
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_7861,c_54,c_55,c_56,c_57,c_913,c_7971,c_7976,c_7981]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9092,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k1_xboole_0
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK8) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_9091]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9379,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
% 19.85/3.00      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK4(sK7,sK8,X0)) = iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7853,c_9092]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11528,plain,
% 19.85/3.00      ( v2_struct_0(sK4(sK7,sK8,X0)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
% 19.85/3.00      | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_9379,c_54,c_55,c_56,c_57]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11529,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
% 19.85/3.00      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK4(sK7,sK8,X0)) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_11528]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9383,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK4(sK7,X0,X1)) != iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7853,c_7837]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_11534,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
% 19.85/3.00      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_11529,c_9383]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_23987,plain,
% 19.85/3.00      ( v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
% 19.85/3.00      | r3_waybel_9(sK7,sK8,X0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_11534,c_54,c_55,c_56,c_57]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_23988,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,X0)) = k1_xboole_0
% 19.85/3.00      | r3_waybel_9(sK7,sK8,X0) != iProver_top
% 19.85/3.00      | m1_subset_1(X0,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_23987]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_23993,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7854,c_23988]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_28,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 19.85/3.00      | ~ v1_compts_1(X1)
% 19.85/3.00      | ~ v2_pre_topc(X1)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f96]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1821,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,X1)
% 19.85/3.00      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 19.85/3.00      | ~ v1_compts_1(X1)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(X1)
% 19.85/3.00      | sK7 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_28,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1822,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1821]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1826,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1822,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1827,plain,
% 19.85/3.00      ( ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | m1_subset_1(sK5(sK7,X0),u1_struct_0(sK7))
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1826]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7956,plain,
% 19.85/3.00      ( ~ l1_waybel_0(sK8,sK7)
% 19.85/3.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7))
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK8)
% 19.85/3.00      | ~ v4_orders_2(sK8)
% 19.85/3.00      | ~ v7_waybel_0(sK8) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1827]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7957,plain,
% 19.85/3.00      ( l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_7956]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24424,plain,
% 19.85/3.00      ( v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0 ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_23993,c_54,c_55,c_56,c_57,c_7957]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24425,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_24424]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_44220,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0 ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_44216,c_24425]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_25,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
% 19.85/3.00      | ~ v2_pre_topc(X0)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0) ),
% 19.85/3.00      inference(cnf_transformation,[],[f95]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1579,plain,
% 19.85/3.00      ( ~ r3_waybel_9(X0,X1,X2)
% 19.85/3.00      | ~ l1_waybel_0(X1,X0)
% 19.85/3.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 19.85/3.00      | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(X1)
% 19.85/3.00      | ~ v4_orders_2(X1)
% 19.85/3.00      | ~ v7_waybel_0(X1)
% 19.85/3.00      | ~ l1_pre_topc(X0)
% 19.85/3.00      | sK7 != X0 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_25,c_43]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1580,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1)))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | v2_struct_0(sK7)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ l1_pre_topc(sK7) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_1579]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1584,plain,
% 19.85/3.00      ( ~ v7_waybel_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1)))
% 19.85/3.00      | v2_struct_0(X0) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_1580,c_44,c_42]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_1585,plain,
% 19.85/3.00      ( ~ r3_waybel_9(sK7,X0,X1)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ m1_subset_1(X1,u1_struct_0(sK7))
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1)))
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_1584]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7852,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,X0,X1) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(X1,u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(X1,k10_yellow_6(sK7,sK4(sK7,X0,X1))) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_1585]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_47030,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK5(sK7,sK8),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK5(sK7,sK8),k1_xboole_0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_44220,c_7852]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7967,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8))
% 19.85/3.00      | ~ l1_waybel_0(sK8,sK7)
% 19.85/3.00      | ~ v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK8)
% 19.85/3.00      | ~ v4_orders_2(sK8)
% 19.85/3.00      | ~ v7_waybel_0(sK8) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_1522]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7968,plain,
% 19.85/3.00      ( r3_waybel_9(sK7,sK8,sK5(sK7,sK8)) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK8,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK8) = iProver_top
% 19.85/3.00      | v4_orders_2(sK8) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK8) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_7967]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_47125,plain,
% 19.85/3.00      ( r2_hidden(sK5(sK7,sK8),k1_xboole_0) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_47030,c_54,c_55,c_56,c_57,c_1430,c_1444,c_1458,c_1472,
% 19.85/3.00                 c_7957,c_7968,c_8238,c_8301,c_8438,c_8574,c_8600,c_9868,
% 19.85/3.00                 c_9874,c_9966,c_9979,c_11584,c_12503,c_12554,c_12576,c_12580,
% 19.85/3.00                 c_12582,c_20405,c_31643,c_43244]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14283,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_13782,c_7855]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9000,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK9(sK6(sK7)))
% 19.85/3.00      | l1_waybel_0(X0,sK7)
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2135]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9001,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_9000]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8999,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK9(sK6(sK7)))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2161]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9005,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) = iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8999]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8998,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK9(sK6(sK7)))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2187]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9009,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8998]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14331,plain,
% 19.85/3.00      ( v4_orders_2(X1) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_14283,c_1430,c_1444,c_1458,c_1472,c_8238,c_8420,c_8600,
% 19.85/3.00                 c_8733,c_9001,c_9005,c_9009,c_9868]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14332,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | r2_hidden(sK1(sK7,X1,k10_yellow_6(sK7,X0)),k10_yellow_6(sK7,X1)) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_14331]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14341,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X1,sK1(sK7,X1,k10_yellow_6(sK7,X0))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X1,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X1,k10_yellow_6(sK7,X0)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X1) != iProver_top
% 19.85/3.00      | v7_waybel_0(X1) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_14332,c_9101]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14359,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X0,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7842,c_14341]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_14510,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_14359,c_7851]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16710,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | r3_waybel_9(sK7,X2,sK1(sK7,X0,k10_yellow_6(sK7,X1))) = iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,X2) != iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(X2,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X2) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(X2) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X2) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7842,c_14510]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16765,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_16710,c_7855]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8154,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8153]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8152,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK6(sK7))
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | v7_waybel_0(X0)
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2161]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8158,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) = iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8152]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8151,plain,
% 19.85/3.00      ( ~ m2_yellow_6(X0,sK7,sK6(sK7))
% 19.85/3.00      | ~ l1_waybel_0(sK6(sK7),sK7)
% 19.85/3.00      | v2_struct_0(sK6(sK7))
% 19.85/3.00      | v4_orders_2(X0)
% 19.85/3.00      | ~ v4_orders_2(sK6(sK7))
% 19.85/3.00      | ~ v7_waybel_0(sK6(sK7)) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2187]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8162,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_8151]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16772,plain,
% 19.85/3.00      ( v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1) ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_16765,c_1430,c_1444,c_1458,c_1472,c_8154,c_8158,c_8162]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16773,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(sK1(sK7,X0,k10_yellow_6(sK7,X1)),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_16772]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16778,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7842,c_16773]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17023,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_16778,c_1430,c_1444,c_1458,c_1472,c_8154,c_8158,c_8162]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17024,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | m1_subset_1(k10_yellow_6(sK7,X1),k1_zfmisc_1(u1_struct_0(sK7))) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_17023]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17030,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7846,c_17024]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_5,plain,
% 19.85/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.85/3.00      inference(cnf_transformation,[],[f73]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_7870,plain,
% 19.85/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.85/3.00      | r1_tarski(X0,X1) = iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_8414,plain,
% 19.85/3.00      ( l1_waybel_0(X0,sK7) != iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,X0),u1_struct_0(sK7)) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v4_orders_2(X0) != iProver_top
% 19.85/3.00      | v7_waybel_0(X0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7846,c_7870]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17029,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | r1_tarski(k10_yellow_6(sK7,X0),u1_struct_0(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7871,c_17024]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17038,plain,
% 19.85/3.00      ( m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_17030,c_1430,c_1444,c_1458,c_1472,c_8238,c_8420,c_8600,
% 19.85/3.00                 c_8733,c_9001,c_9005,c_9009,c_9868]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17039,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,X0) = k10_yellow_6(sK7,X1)
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | m2_yellow_6(X1,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(X1) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_17038]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17044,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK9(sK6(sK7)))) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_17039]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9028,plain,
% 19.85/3.00      ( m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7)))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | v1_compts_1(sK7)
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_41]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_9086,plain,
% 19.85/3.00      ( m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_9028]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_10947,plain,
% 19.85/3.00      ( ~ m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,X0)
% 19.85/3.00      | ~ l1_waybel_0(X0,sK7)
% 19.85/3.00      | v2_struct_0(X0)
% 19.85/3.00      | ~ v2_struct_0(sK9(sK9(sK6(sK7))))
% 19.85/3.00      | ~ v4_orders_2(X0)
% 19.85/3.00      | ~ v7_waybel_0(X0) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_2213]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16686,plain,
% 19.85/3.00      ( ~ m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7)))
% 19.85/3.00      | ~ l1_waybel_0(sK9(sK6(sK7)),sK7)
% 19.85/3.00      | ~ v2_struct_0(sK9(sK9(sK6(sK7))))
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v4_orders_2(sK9(sK6(sK7)))
% 19.85/3.00      | ~ v7_waybel_0(sK9(sK6(sK7))) ),
% 19.85/3.00      inference(instantiation,[status(thm)],[c_10947]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_16687,plain,
% 19.85/3.00      ( m2_yellow_6(sK9(sK9(sK6(sK7))),sK7,sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | l1_waybel_0(sK9(sK6(sK7)),sK7) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK9(sK6(sK7)))) != iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK9(sK6(sK7))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK9(sK6(sK7))) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_16686]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17814,plain,
% 19.85/3.00      ( m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_17044,c_1430,c_1444,c_1458,c_1472,c_8238,c_8420,c_8600,
% 19.85/3.00                 c_8733,c_9086,c_9868,c_16687]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17815,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,X0)
% 19.85/3.00      | m2_yellow_6(X0,sK7,sK6(sK7)) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(X0) = iProver_top ),
% 19.85/3.00      inference(renaming,[status(thm)],[c_17814]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17820,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7)))
% 19.85/3.00      | l1_waybel_0(sK6(sK7),sK7) != iProver_top
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top
% 19.85/3.00      | v2_struct_0(sK9(sK6(sK7))) = iProver_top
% 19.85/3.00      | v2_struct_0(sK6(sK7)) = iProver_top
% 19.85/3.00      | v4_orders_2(sK6(sK7)) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK6(sK7)) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_7863,c_17815]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_17824,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7)))
% 19.85/3.00      | v1_compts_1(sK7) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_17820,c_1430,c_1444,c_1458,c_1472,c_9979]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24429,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK4(sK7,sK8,sK5(sK7,sK8))) = k1_xboole_0
% 19.85/3.00      | k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7))) ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_17824,c_24425]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24559,plain,
% 19.85/3.00      ( k10_yellow_6(sK7,sK9(sK9(sK6(sK7)))) = k10_yellow_6(sK7,sK9(sK6(sK7)))
% 19.85/3.00      | l1_waybel_0(sK4(sK7,sK8,sK5(sK7,sK8)),sK7) != iProver_top
% 19.85/3.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top
% 19.85/3.00      | v2_struct_0(sK4(sK7,sK8,sK5(sK7,sK8))) = iProver_top
% 19.85/3.00      | v4_orders_2(sK4(sK7,sK8,sK5(sK7,sK8))) != iProver_top
% 19.85/3.00      | v7_waybel_0(sK4(sK7,sK8,sK5(sK7,sK8))) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_24429,c_7846]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24800,plain,
% 19.85/3.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK7))) = iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,
% 19.85/3.00                [status(thm)],
% 19.85/3.00                [c_24559,c_8438,c_8574]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24805,plain,
% 19.85/3.00      ( m1_subset_1(X0,u1_struct_0(sK7)) = iProver_top
% 19.85/3.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_24800,c_7869]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_727,plain,
% 19.85/3.00      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 19.85/3.00      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_728,plain,
% 19.85/3.00      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 19.85/3.00      inference(unflattening,[status(thm)],[c_727]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_729,plain,
% 19.85/3.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.85/3.00      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_24813,plain,
% 19.85/3.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 19.85/3.00      inference(global_propositional_subsumption,[status(thm)],[c_24805,c_729]) ).
% 19.85/3.00  
% 19.85/3.00  cnf(c_47132,plain,
% 19.85/3.00      ( $false ),
% 19.85/3.00      inference(superposition,[status(thm)],[c_47125,c_24813]) ).
% 19.85/3.00  
% 19.85/3.00  
% 19.85/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.85/3.00  
% 19.85/3.00  ------                               Statistics
% 19.85/3.00  
% 19.85/3.00  ------ General
% 19.85/3.00  
% 19.85/3.00  abstr_ref_over_cycles:                  0
% 19.85/3.00  abstr_ref_under_cycles:                 0
% 19.85/3.00  gc_basic_clause_elim:                   0
% 19.85/3.00  forced_gc_time:                         0
% 19.85/3.00  parsing_time:                           0.014
% 19.85/3.00  unif_index_cands_time:                  0.
% 19.85/3.00  unif_index_add_time:                    0.
% 19.85/3.00  orderings_time:                         0.
% 19.85/3.00  out_proof_time:                         0.045
% 19.85/3.00  total_time:                             2.486
% 19.85/3.00  num_of_symbols:                         62
% 19.85/3.00  num_of_terms:                           50812
% 19.85/3.00  
% 19.85/3.00  ------ Preprocessing
% 19.85/3.00  
% 19.85/3.00  num_of_splits:                          0
% 19.85/3.00  num_of_split_atoms:                     0
% 19.85/3.00  num_of_reused_defs:                     0
% 19.85/3.00  num_eq_ax_congr_red:                    55
% 19.85/3.00  num_of_sem_filtered_clauses:            1
% 19.85/3.00  num_of_subtypes:                        0
% 19.85/3.00  monotx_restored_types:                  0
% 19.85/3.00  sat_num_of_epr_types:                   0
% 19.85/3.00  sat_num_of_non_cyclic_types:            0
% 19.85/3.00  sat_guarded_non_collapsed_types:        0
% 19.85/3.00  num_pure_diseq_elim:                    0
% 19.85/3.00  simp_replaced_by:                       0
% 19.85/3.00  res_preprocessed:                       214
% 19.85/3.00  prep_upred:                             0
% 19.85/3.00  prep_unflattend:                        170
% 19.85/3.00  smt_new_axioms:                         0
% 19.85/3.00  pred_elim_cands:                        12
% 19.85/3.00  pred_elim:                              4
% 19.85/3.00  pred_elim_cl:                           5
% 19.85/3.00  pred_elim_cycles:                       16
% 19.85/3.00  merged_defs:                            8
% 19.85/3.00  merged_defs_ncl:                        0
% 19.85/3.00  bin_hyper_res:                          8
% 19.85/3.00  prep_cycles:                            4
% 19.85/3.00  pred_elim_time:                         0.099
% 19.85/3.00  splitting_time:                         0.
% 19.85/3.00  sem_filter_time:                        0.
% 19.85/3.00  monotx_time:                            0.001
% 19.85/3.00  subtype_inf_time:                       0.
% 19.85/3.00  
% 19.85/3.00  ------ Problem properties
% 19.85/3.00  
% 19.85/3.00  clauses:                                40
% 19.85/3.00  conjectures:                            6
% 19.85/3.00  epr:                                    12
% 19.85/3.00  horn:                                   15
% 19.85/3.00  ground:                                 10
% 19.85/3.00  unary:                                  2
% 19.85/3.00  binary:                                 14
% 19.85/3.00  lits:                                   182
% 19.85/3.00  lits_eq:                                6
% 19.85/3.00  fd_pure:                                0
% 19.85/3.00  fd_pseudo:                              0
% 19.85/3.00  fd_cond:                                0
% 19.85/3.00  fd_pseudo_cond:                         4
% 19.85/3.00  ac_symbols:                             0
% 19.85/3.00  
% 19.85/3.00  ------ Propositional Solver
% 19.85/3.00  
% 19.85/3.00  prop_solver_calls:                      35
% 19.85/3.00  prop_fast_solver_calls:                 10639
% 19.85/3.00  smt_solver_calls:                       0
% 19.85/3.00  smt_fast_solver_calls:                  0
% 19.85/3.00  prop_num_of_clauses:                    18737
% 19.85/3.00  prop_preprocess_simplified:             44175
% 19.85/3.00  prop_fo_subsumed:                       864
% 19.85/3.00  prop_solver_time:                       0.
% 19.85/3.00  smt_solver_time:                        0.
% 19.85/3.00  smt_fast_solver_time:                   0.
% 19.85/3.00  prop_fast_solver_time:                  0.
% 19.85/3.00  prop_unsat_core_time:                   0.
% 19.85/3.00  
% 19.85/3.00  ------ QBF
% 19.85/3.00  
% 19.85/3.00  qbf_q_res:                              0
% 19.85/3.00  qbf_num_tautologies:                    0
% 19.85/3.00  qbf_prep_cycles:                        0
% 19.85/3.00  
% 19.85/3.00  ------ BMC1
% 19.85/3.00  
% 19.85/3.00  bmc1_current_bound:                     -1
% 19.85/3.00  bmc1_last_solved_bound:                 -1
% 19.85/3.00  bmc1_unsat_core_size:                   -1
% 19.85/3.00  bmc1_unsat_core_parents_size:           -1
% 19.85/3.00  bmc1_merge_next_fun:                    0
% 19.85/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.85/3.00  
% 19.85/3.00  ------ Instantiation
% 19.85/3.00  
% 19.85/3.00  inst_num_of_clauses:                    4909
% 19.85/3.00  inst_num_in_passive:                    2981
% 19.85/3.00  inst_num_in_active:                     1921
% 19.85/3.00  inst_num_in_unprocessed:                7
% 19.85/3.00  inst_num_of_loops:                      2460
% 19.85/3.00  inst_num_of_learning_restarts:          0
% 19.85/3.00  inst_num_moves_active_passive:          533
% 19.85/3.00  inst_lit_activity:                      0
% 19.85/3.00  inst_lit_activity_moves:                1
% 19.85/3.00  inst_num_tautologies:                   0
% 19.85/3.00  inst_num_prop_implied:                  0
% 19.85/3.00  inst_num_existing_simplified:           0
% 19.85/3.00  inst_num_eq_res_simplified:             0
% 19.85/3.00  inst_num_child_elim:                    0
% 19.85/3.00  inst_num_of_dismatching_blockings:      2236
% 19.85/3.00  inst_num_of_non_proper_insts:           5272
% 19.85/3.00  inst_num_of_duplicates:                 0
% 19.85/3.00  inst_inst_num_from_inst_to_res:         0
% 19.85/3.00  inst_dismatching_checking_time:         0.
% 19.85/3.00  
% 19.85/3.00  ------ Resolution
% 19.85/3.00  
% 19.85/3.00  res_num_of_clauses:                     0
% 19.85/3.00  res_num_in_passive:                     0
% 19.85/3.00  res_num_in_active:                      0
% 19.85/3.00  res_num_of_loops:                       218
% 19.85/3.00  res_forward_subset_subsumed:            74
% 19.85/3.00  res_backward_subset_subsumed:           0
% 19.85/3.00  res_forward_subsumed:                   0
% 19.85/3.00  res_backward_subsumed:                  1
% 19.85/3.00  res_forward_subsumption_resolution:     15
% 19.85/3.00  res_backward_subsumption_resolution:    6
% 19.85/3.00  res_clause_to_clause_subsumption:       20930
% 19.85/3.00  res_orphan_elimination:                 0
% 19.85/3.00  res_tautology_del:                      242
% 19.85/3.00  res_num_eq_res_simplified:              0
% 19.85/3.00  res_num_sel_changes:                    0
% 19.85/3.00  res_moves_from_active_to_pass:          0
% 19.85/3.00  
% 19.85/3.00  ------ Superposition
% 19.85/3.00  
% 19.85/3.00  sup_time_total:                         0.
% 19.85/3.00  sup_time_generating:                    0.
% 19.85/3.00  sup_time_sim_full:                      0.
% 19.85/3.00  sup_time_sim_immed:                     0.
% 19.85/3.00  
% 19.85/3.00  sup_num_of_clauses:                     1437
% 19.85/3.00  sup_num_in_active:                      171
% 19.85/3.00  sup_num_in_passive:                     1266
% 19.85/3.00  sup_num_of_loops:                       490
% 19.85/3.00  sup_fw_superposition:                   1174
% 19.85/3.00  sup_bw_superposition:                   1229
% 19.85/3.00  sup_immediate_simplified:               531
% 19.85/3.00  sup_given_eliminated:                   5
% 19.85/3.00  comparisons_done:                       0
% 19.85/3.00  comparisons_avoided:                    22
% 19.85/3.00  
% 19.85/3.00  ------ Simplifications
% 19.85/3.00  
% 19.85/3.00  
% 19.85/3.00  sim_fw_subset_subsumed:                 132
% 19.85/3.00  sim_bw_subset_subsumed:                 36
% 19.85/3.00  sim_fw_subsumed:                        260
% 19.85/3.00  sim_bw_subsumed:                        322
% 19.85/3.00  sim_fw_subsumption_res:                 0
% 19.85/3.00  sim_bw_subsumption_res:                 0
% 19.85/3.00  sim_tautology_del:                      67
% 19.85/3.00  sim_eq_tautology_del:                   115
% 19.85/3.00  sim_eq_res_simp:                        3
% 19.85/3.00  sim_fw_demodulated:                     4
% 19.85/3.00  sim_bw_demodulated:                     0
% 19.85/3.00  sim_light_normalised:                   143
% 19.85/3.00  sim_joinable_taut:                      0
% 19.85/3.00  sim_joinable_simp:                      0
% 19.85/3.00  sim_ac_normalised:                      0
% 19.85/3.00  sim_smt_subsumption:                    0
% 19.85/3.00  
%------------------------------------------------------------------------------
