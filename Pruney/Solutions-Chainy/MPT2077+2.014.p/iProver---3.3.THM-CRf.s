%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:27 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_63)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f38])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f60,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK8(X3),X0)
        & m2_yellow_6(sK8(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
            | ~ m2_yellow_6(X2,X0,sK7) )
        & l1_waybel_0(sK7,X0)
        & v7_waybel_0(sK7)
        & v4_orders_2(sK7)
        & ~ v2_struct_0(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
                ( ~ v3_yellow_6(X2,sK6)
                | ~ m2_yellow_6(X2,sK6,X1) )
            & l1_waybel_0(X1,sK6)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK6) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK6)
                & m2_yellow_6(X4,sK6,X3) )
            | ~ l1_waybel_0(X3,sK6)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK6) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK6)
            | ~ m2_yellow_6(X2,sK6,sK7) )
        & l1_waybel_0(sK7,sK6)
        & v7_waybel_0(sK7)
        & v4_orders_2(sK7)
        & ~ v2_struct_0(sK7) )
      | ~ v1_compts_1(sK6) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK8(X3),sK6)
            & m2_yellow_6(sK8(X3),sK6,X3) )
          | ~ l1_waybel_0(X3,sK6)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK6) )
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f57,f60,f59,f58])).

fof(f95,plain,(
    ! [X3] :
      ( m2_yellow_6(sK8(X3),sK6,X3)
      | ~ l1_waybel_0(X3,sK6)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(ennf_transformation,[],[f6])).

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
    inference(flattening,[],[f22])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f40])).

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
    inference(rectify,[],[f41])).

fof(f45,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f92,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f94,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f61])).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f69])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f30])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f32])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f53,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
            ( ~ r3_waybel_9(X0,sK4(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK4(X0),X0)
        & v7_waybel_0(sK4(X0))
        & v4_orders_2(sK4(X0))
        & ~ v2_struct_0(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK4(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK4(X0),X0)
            & v7_waybel_0(sK4(X0))
            & v4_orders_2(sK4(X0))
            & ~ v2_struct_0(sK4(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK5(X0,X3))
                & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).

fof(f91,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f87,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f90,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK4(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f28])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
    ! [X3] :
      ( v3_yellow_6(sK8(X3),sK6)
      | ~ l1_waybel_0(X3,sK6)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f86,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK5(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
        & m2_yellow_6(sK3(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f48])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK6)
      | ~ m2_yellow_6(X2,sK6,sK7)
      | ~ v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,
    ( ~ v2_struct_0(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,
    ( v4_orders_2(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,
    ( v7_waybel_0(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,
    ( l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

fof(f85,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f49])).

cnf(c_36,negated_conjecture,
    ( m2_yellow_6(sK8(X0),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_8707,plain,
    ( m2_yellow_6(sK8(X0),sK6,X0) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

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
    inference(cnf_transformation,[],[f70])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1612,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_38])).

cnf(c_1613,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1612])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1617,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1613,c_39,c_37])).

cnf(c_1618,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1617])).

cnf(c_8686,plain,
    ( k10_yellow_6(sK6,X0) = X1
    | l1_waybel_0(X0,sK6) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1618])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1537,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_38])).

cnf(c_1538,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1537])).

cnf(c_1542,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1538,c_39,c_37])).

cnf(c_1543,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1542])).

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
    inference(cnf_transformation,[],[f103])).

cnf(c_1363,plain,
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
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_38])).

cnf(c_1364,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1363])).

cnf(c_1368,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1364,c_39,c_37])).

cnf(c_1369,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1368])).

cnf(c_1560,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1543,c_1369])).

cnf(c_8689,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK6,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1560])).

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
    inference(cnf_transformation,[],[f71])).

cnf(c_1645,plain,
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
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_38])).

cnf(c_1646,plain,
    ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(unflattening,[status(thm)],[c_1645])).

cnf(c_1650,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1646,c_39,c_37])).

cnf(c_1651,plain,
    ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(renaming,[status(thm)],[c_1650])).

cnf(c_8685,plain,
    ( k10_yellow_6(sK6,X0) = X1
    | m1_connsp_2(X2,sK6,sK0(sK6,X0,X1)) != iProver_top
    | r1_waybel_0(sK6,X0,X2) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_11342,plain,
    ( k10_yellow_6(sK6,X0) = X1
    | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
    | l1_waybel_0(X2,sK6) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8689,c_8685])).

cnf(c_2155,plain,
    ( r1_waybel_0(sK6,X0,X1)
    | ~ l1_waybel_0(X2,sK6)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X3,k10_yellow_6(sK6,X2))
    | r2_hidden(sK0(sK6,X0,X4),X4)
    | ~ m1_subset_1(X3,u1_struct_0(sK6))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ v7_waybel_0(X0)
    | sK2(sK6,X2,X3) != X1
    | sK0(sK6,X0,X4) != X3
    | k10_yellow_6(sK6,X0) = X4
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_1560,c_1651])).

cnf(c_2156,plain,
    ( r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,X2)))
    | ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X0,X2),X2)
    | r2_hidden(sK0(sK6,X0,X2),k10_yellow_6(sK6,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK0(sK6,X0,X2),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = X2 ),
    inference(unflattening,[status(thm)],[c_2155])).

cnf(c_2188,plain,
    ( r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,X2)))
    | ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X0,X2),X2)
    | r2_hidden(sK0(sK6,X0,X2),k10_yellow_6(sK6,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2156,c_1618])).

cnf(c_2202,plain,
    ( k10_yellow_6(sK6,X0) = X1
    | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | l1_waybel_0(X2,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2188])).

cnf(c_11920,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
    | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | l1_waybel_0(X2,sK6) != iProver_top
    | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
    | k10_yellow_6(sK6,X0) = X1
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11342,c_2202])).

cnf(c_11921,plain,
    ( k10_yellow_6(sK6,X0) = X1
    | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | l1_waybel_0(X2,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
    | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_11920])).

cnf(c_0,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8713,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_442,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X1 != X2
    | X0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_8705,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_9307,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8713,c_8705])).

cnf(c_11940,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X1)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11921,c_9307])).

cnf(c_9421,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9424,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9421])).

cnf(c_12518,plain,
    ( r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X1)) = iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,k1_xboole_0))) = iProver_top
    | k10_yellow_6(sK6,X0) = k1_xboole_0
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11940,c_9424])).

cnf(c_12519,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X1)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_12518])).

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
    inference(cnf_transformation,[],[f102])).

cnf(c_1399,plain,
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
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_38])).

cnf(c_1400,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1399])).

cnf(c_1404,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1400,c_39,c_37])).

cnf(c_1405,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1404])).

cnf(c_1561,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1543,c_1405])).

cnf(c_8688,plain,
    ( r1_waybel_0(sK6,X0,sK2(sK6,X0,X1)) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK6,X0)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_12535,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X0)) = iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12519,c_8688])).

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
    inference(cnf_transformation,[],[f81])).

cnf(c_1330,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_1331,plain,
    ( r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1330])).

cnf(c_1335,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1331,c_39,c_37])).

cnf(c_1336,plain,
    ( r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1335])).

cnf(c_8694,plain,
    ( r3_waybel_9(sK6,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_1337,plain,
    ( r3_waybel_9(sK6,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1336])).

cnf(c_8690,plain,
    ( l1_waybel_0(X0,sK6) != iProver_top
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1543])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8712,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9531,plain,
    ( l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8690,c_8712])).

cnf(c_10344,plain,
    ( r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r3_waybel_9(sK6,X0,X1) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8694,c_1337,c_9531])).

cnf(c_10345,plain,
    ( r3_waybel_9(sK6,X0,X1) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10344])).

cnf(c_12692,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12535,c_10345])).

cnf(c_12795,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8686,c_12692])).

cnf(c_12800,plain,
    ( l1_waybel_0(X0,sK6) != iProver_top
    | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | k10_yellow_6(sK6,X0) = k1_xboole_0
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12795,c_9424])).

cnf(c_12801,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12800])).

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
    inference(cnf_transformation,[],[f82])).

cnf(c_1298,plain,
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
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_38])).

cnf(c_1299,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1301,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_39,c_37])).

cnf(c_1302,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1301])).

cnf(c_8695,plain,
    ( r3_waybel_9(sK6,X0,X1) != iProver_top
    | r3_waybel_9(sK6,X2,X1) = iProver_top
    | m2_yellow_6(X0,sK6,X2) != iProver_top
    | l1_waybel_0(X2,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v4_orders_2(X2) != iProver_top
    | v7_waybel_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_12813,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12801,c_8695])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_541,plain,
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

cnf(c_542,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_541])).

cnf(c_1814,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_37])).

cnf(c_1815,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1814])).

cnf(c_1817,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1815,c_39])).

cnf(c_1818,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X0,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1817])).

cnf(c_1819,plain,
    ( m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | l1_waybel_0(X0,sK6) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_513,plain,
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

cnf(c_514,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_1840,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_514,c_37])).

cnf(c_1841,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1840])).

cnf(c_1843,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1841,c_39])).

cnf(c_1844,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1843])).

cnf(c_1845,plain,
    ( m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top
    | v7_waybel_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1844])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_485,plain,
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

cnf(c_486,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1866,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_486,c_37])).

cnf(c_1867,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1866])).

cnf(c_1869,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1867,c_39])).

cnf(c_1870,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1869])).

cnf(c_1871,plain,
    ( m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v4_orders_2(X0) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_457,plain,
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

cnf(c_458,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1892,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_458,c_37])).

cnf(c_1893,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1892])).

cnf(c_1895,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1893,c_39])).

cnf(c_1896,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1895])).

cnf(c_1897,plain,
    ( m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1896])).

cnf(c_13244,plain,
    ( v4_orders_2(X1) != iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK6,X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12813,c_1819,c_1845,c_1871,c_1897])).

cnf(c_13245,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13244])).

cnf(c_13256,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X0) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8686,c_13245])).

cnf(c_13313,plain,
    ( v4_orders_2(X1) != iProver_top
    | m2_yellow_6(X0,sK6,X1) != iProver_top
    | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | k10_yellow_6(sK6,X0) = k1_xboole_0
    | l1_waybel_0(X1,sK6) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13256,c_1819,c_1845,c_1871,c_1897,c_9424])).

cnf(c_13314,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13313])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1211,plain,
    ( ~ r3_waybel_9(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_1212,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1211])).

cnf(c_1216,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1212,c_39,c_37])).

cnf(c_8698,plain,
    ( r3_waybel_9(sK6,sK4(sK6),X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_13326,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13314,c_8698])).

cnf(c_27,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1155,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_1156,plain,
    ( v1_compts_1(sK6)
    | ~ v2_struct_0(sK4(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1155])).

cnf(c_1158,plain,
    ( v1_compts_1(sK6)
    | ~ v2_struct_0(sK4(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1156,c_39,c_38,c_37,c_63])).

cnf(c_1160,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1158])).

cnf(c_26,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1169,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_1170,plain,
    ( v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | v4_orders_2(sK4(sK6))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1169])).

cnf(c_1172,plain,
    ( v4_orders_2(sK4(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_39,c_37])).

cnf(c_1173,plain,
    ( v1_compts_1(sK6)
    | v4_orders_2(sK4(sK6)) ),
    inference(renaming,[status(thm)],[c_1172])).

cnf(c_1174,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v4_orders_2(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_25,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1183,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_38])).

cnf(c_1184,plain,
    ( v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | v7_waybel_0(sK4(sK6))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1183])).

cnf(c_1186,plain,
    ( v7_waybel_0(sK4(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1184,c_39,c_37])).

cnf(c_1187,plain,
    ( v1_compts_1(sK6)
    | v7_waybel_0(sK4(sK6)) ),
    inference(renaming,[status(thm)],[c_1186])).

cnf(c_1188,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v7_waybel_0(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1187])).

cnf(c_24,plain,
    ( l1_waybel_0(sK4(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1197,plain,
    ( l1_waybel_0(sK4(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_1198,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1197])).

cnf(c_1200,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_39,c_37])).

cnf(c_1202,plain,
    ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_13413,plain,
    ( v1_compts_1(sK6) = iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13326,c_1160,c_1174,c_1188,c_1202])).

cnf(c_13414,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
    | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_13413])).

cnf(c_13423,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8686,c_13414])).

cnf(c_9323,plain,
    ( ~ m2_yellow_6(X0,sK6,sK4(sK6))
    | l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_9324,plain,
    ( m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(X0,sK6) = iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9323])).

cnf(c_9322,plain,
    ( ~ m2_yellow_6(X0,sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_9328,plain,
    ( m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9322])).

cnf(c_9321,plain,
    ( ~ m2_yellow_6(X0,sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_1870])).

cnf(c_9332,plain,
    ( m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9321])).

cnf(c_13428,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13423,c_1160,c_1174,c_1188,c_1202,c_9324,c_9328,c_9332,c_9424])).

cnf(c_13438,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8707,c_13428])).

cnf(c_2447,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X2,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1818])).

cnf(c_2448,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2447])).

cnf(c_2423,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(X2)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1844])).

cnf(c_2424,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK8(X0)) ),
    inference(unflattening,[status(thm)],[c_2423])).

cnf(c_2399,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | v4_orders_2(X2)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1870])).

cnf(c_2400,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2399])).

cnf(c_2375,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | v1_compts_1(sK6)
    | ~ v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X1 != X0
    | sK8(X0) != X2
    | sK6 != sK6 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_1896])).

cnf(c_2376,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK8(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2375])).

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
    inference(cnf_transformation,[],[f79])).

cnf(c_35,negated_conjecture,
    ( v3_yellow_6(sK8(X0),sK6)
    | ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_639,plain,
    ( ~ l1_waybel_0(X0,X1)
    | ~ l1_waybel_0(X2,sK6)
    | v1_compts_1(sK6)
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
    | sK8(X2) != X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_640,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK8(X0))
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_644,plain,
    ( ~ v7_waybel_0(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v4_orders_2(X0)
    | v1_compts_1(sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | ~ l1_waybel_0(X0,sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_39,c_38,c_37])).

cnf(c_645,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK8(X0))
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_644])).

cnf(c_2630,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2376,c_645])).

cnf(c_2641,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2400,c_2630])).

cnf(c_2652,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2424,c_2641])).

cnf(c_2658,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2448,c_2652])).

cnf(c_9460,plain,
    ( ~ l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6))
    | k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2658])).

cnf(c_9461,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9460])).

cnf(c_8699,plain,
    ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1200])).

cnf(c_8681,plain,
    ( m2_yellow_6(X0,sK6,X1) != iProver_top
    | l1_waybel_0(X1,sK6) != iProver_top
    | v2_struct_0(X0) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v4_orders_2(X1) != iProver_top
    | v7_waybel_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1896])).

cnf(c_9318,plain,
    ( l1_waybel_0(X0,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK8(X0)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8707,c_8681])).

cnf(c_9628,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8699,c_9318])).

cnf(c_10427,plain,
    ( v2_struct_0(sK8(sK4(sK6))) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9628,c_1160,c_1174,c_1188])).

cnf(c_10428,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_10427])).

cnf(c_13481,plain,
    ( v1_compts_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13438,c_1160,c_1174,c_1188,c_1202,c_9461,c_10428])).

cnf(c_28,plain,
    ( r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1125,plain,
    ( r3_waybel_9(X0,X1,sK5(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_38])).

cnf(c_1126,plain,
    ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1125])).

cnf(c_1130,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1126,c_39,c_37])).

cnf(c_1131,plain,
    ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1130])).

cnf(c_8703,plain,
    ( r3_waybel_9(sK6,X0,sK5(sK6,X0)) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

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
    inference(cnf_transformation,[],[f83])).

cnf(c_1232,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_38])).

cnf(c_1233,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1232])).

cnf(c_1237,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1233,c_39,c_37])).

cnf(c_1238,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1237])).

cnf(c_8697,plain,
    ( r3_waybel_9(sK6,X0,X1) != iProver_top
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0) = iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

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
    inference(cnf_transformation,[],[f80])).

cnf(c_30,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ v3_yellow_6(X0,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_606,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(X1,X2)
    | ~ v1_compts_1(sK6)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k10_yellow_6(X2,X1) = k1_xboole_0
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_607,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK6)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m2_yellow_6(X0,sK6,sK7)
    | v2_struct_0(X0)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_39,c_38,c_37])).

cnf(c_612,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_8704,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK7) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_34,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_49,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_50,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v4_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_51,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v7_waybel_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_52,plain,
    ( l1_waybel_0(sK7,sK6) = iProver_top
    | v1_compts_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_613,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK7) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_9148,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_9149,plain,
    ( m2_yellow_6(X0,sK6,sK7) != iProver_top
    | l1_waybel_0(X0,sK6) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9148])).

cnf(c_9153,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | v7_waybel_0(X0)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_9154,plain,
    ( m2_yellow_6(X0,sK6,sK7) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(X0) = iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9153])).

cnf(c_9158,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | v4_orders_2(X0)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1870])).

cnf(c_9159,plain,
    ( m2_yellow_6(X0,sK6,sK7) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(X0) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9158])).

cnf(c_10331,plain,
    ( m2_yellow_6(X0,sK6,sK7) != iProver_top
    | k10_yellow_6(sK6,X0) = k1_xboole_0
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8704,c_49,c_50,c_51,c_52,c_613,c_9149,c_9154,c_9159])).

cnf(c_10332,plain,
    ( k10_yellow_6(sK6,X0) = k1_xboole_0
    | m2_yellow_6(X0,sK6,sK7) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10331])).

cnf(c_10581,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK3(sK6,sK7,X0)) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8697,c_10332])).

cnf(c_10585,plain,
    ( r3_waybel_9(sK6,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3(sK6,X0,X1)) != iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8697,c_8681])).

cnf(c_10651,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10581,c_10585])).

cnf(c_11569,plain,
    ( v1_compts_1(sK6) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10651,c_49,c_50,c_51,c_52])).

cnf(c_11570,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_11569])).

cnf(c_11579,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8703,c_11570])).

cnf(c_29,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1507,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_38])).

cnf(c_1508,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1507])).

cnf(c_1512,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1508,c_39,c_37])).

cnf(c_1513,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1512])).

cnf(c_9136,plain,
    ( ~ l1_waybel_0(sK7,sK6)
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1513])).

cnf(c_9137,plain,
    ( l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) = iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9136])).

cnf(c_11697,plain,
    ( v1_compts_1(sK6) != iProver_top
    | k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11579,c_49,c_50,c_51,c_52,c_9137])).

cnf(c_11698,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
    | v1_compts_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_11697])).

cnf(c_13486,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13481,c_11698])).

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
    inference(cnf_transformation,[],[f84])).

cnf(c_1265,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_1266,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1265])).

cnf(c_1270,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_39,c_37])).

cnf(c_1271,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1270])).

cnf(c_8696,plain,
    ( r3_waybel_9(sK6,X0,X1) != iProver_top
    | l1_waybel_0(X0,sK6) != iProver_top
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1))) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(X0) != iProver_top
    | v7_waybel_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_13704,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_13486,c_8696])).

cnf(c_9145,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_9146,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9145])).

cnf(c_13757,plain,
    ( r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13704,c_49,c_50,c_51,c_52,c_1160,c_1174,c_1188,c_1202,c_9137,c_9146,c_9461,c_10428,c_13438])).

cnf(c_13762,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13757,c_9307])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:38:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.62/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.05  
% 3.62/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/1.05  
% 3.62/1.05  ------  iProver source info
% 3.62/1.05  
% 3.62/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.62/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/1.05  git: non_committed_changes: false
% 3.62/1.05  git: last_make_outside_of_git: false
% 3.62/1.05  
% 3.62/1.05  ------ 
% 3.62/1.05  
% 3.62/1.05  ------ Input Options
% 3.62/1.05  
% 3.62/1.05  --out_options                           all
% 3.62/1.05  --tptp_safe_out                         true
% 3.62/1.05  --problem_path                          ""
% 3.62/1.05  --include_path                          ""
% 3.62/1.05  --clausifier                            res/vclausify_rel
% 3.62/1.05  --clausifier_options                    --mode clausify
% 3.62/1.05  --stdin                                 false
% 3.62/1.05  --stats_out                             all
% 3.62/1.05  
% 3.62/1.05  ------ General Options
% 3.62/1.05  
% 3.62/1.05  --fof                                   false
% 3.62/1.05  --time_out_real                         305.
% 3.62/1.05  --time_out_virtual                      -1.
% 3.62/1.05  --symbol_type_check                     false
% 3.62/1.05  --clausify_out                          false
% 3.62/1.05  --sig_cnt_out                           false
% 3.62/1.05  --trig_cnt_out                          false
% 3.62/1.05  --trig_cnt_out_tolerance                1.
% 3.62/1.05  --trig_cnt_out_sk_spl                   false
% 3.62/1.05  --abstr_cl_out                          false
% 3.62/1.05  
% 3.62/1.05  ------ Global Options
% 3.62/1.05  
% 3.62/1.05  --schedule                              default
% 3.62/1.05  --add_important_lit                     false
% 3.62/1.05  --prop_solver_per_cl                    1000
% 3.62/1.05  --min_unsat_core                        false
% 3.62/1.05  --soft_assumptions                      false
% 3.62/1.05  --soft_lemma_size                       3
% 3.62/1.05  --prop_impl_unit_size                   0
% 3.62/1.05  --prop_impl_unit                        []
% 3.62/1.05  --share_sel_clauses                     true
% 3.62/1.05  --reset_solvers                         false
% 3.62/1.05  --bc_imp_inh                            [conj_cone]
% 3.62/1.05  --conj_cone_tolerance                   3.
% 3.62/1.05  --extra_neg_conj                        none
% 3.62/1.05  --large_theory_mode                     true
% 3.62/1.05  --prolific_symb_bound                   200
% 3.62/1.05  --lt_threshold                          2000
% 3.62/1.05  --clause_weak_htbl                      true
% 3.62/1.05  --gc_record_bc_elim                     false
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing Options
% 3.62/1.05  
% 3.62/1.05  --preprocessing_flag                    true
% 3.62/1.05  --time_out_prep_mult                    0.1
% 3.62/1.05  --splitting_mode                        input
% 3.62/1.05  --splitting_grd                         true
% 3.62/1.05  --splitting_cvd                         false
% 3.62/1.05  --splitting_cvd_svl                     false
% 3.62/1.05  --splitting_nvd                         32
% 3.62/1.05  --sub_typing                            true
% 3.62/1.05  --prep_gs_sim                           true
% 3.62/1.05  --prep_unflatten                        true
% 3.62/1.05  --prep_res_sim                          true
% 3.62/1.05  --prep_upred                            true
% 3.62/1.05  --prep_sem_filter                       exhaustive
% 3.62/1.05  --prep_sem_filter_out                   false
% 3.62/1.05  --pred_elim                             true
% 3.62/1.05  --res_sim_input                         true
% 3.62/1.05  --eq_ax_congr_red                       true
% 3.62/1.05  --pure_diseq_elim                       true
% 3.62/1.05  --brand_transform                       false
% 3.62/1.05  --non_eq_to_eq                          false
% 3.62/1.05  --prep_def_merge                        true
% 3.62/1.05  --prep_def_merge_prop_impl              false
% 3.62/1.05  --prep_def_merge_mbd                    true
% 3.62/1.05  --prep_def_merge_tr_red                 false
% 3.62/1.05  --prep_def_merge_tr_cl                  false
% 3.62/1.05  --smt_preprocessing                     true
% 3.62/1.05  --smt_ac_axioms                         fast
% 3.62/1.05  --preprocessed_out                      false
% 3.62/1.05  --preprocessed_stats                    false
% 3.62/1.05  
% 3.62/1.05  ------ Abstraction refinement Options
% 3.62/1.05  
% 3.62/1.05  --abstr_ref                             []
% 3.62/1.05  --abstr_ref_prep                        false
% 3.62/1.05  --abstr_ref_until_sat                   false
% 3.62/1.05  --abstr_ref_sig_restrict                funpre
% 3.62/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.05  --abstr_ref_under                       []
% 3.62/1.05  
% 3.62/1.05  ------ SAT Options
% 3.62/1.05  
% 3.62/1.05  --sat_mode                              false
% 3.62/1.05  --sat_fm_restart_options                ""
% 3.62/1.05  --sat_gr_def                            false
% 3.62/1.05  --sat_epr_types                         true
% 3.62/1.05  --sat_non_cyclic_types                  false
% 3.62/1.05  --sat_finite_models                     false
% 3.62/1.05  --sat_fm_lemmas                         false
% 3.62/1.05  --sat_fm_prep                           false
% 3.62/1.05  --sat_fm_uc_incr                        true
% 3.62/1.05  --sat_out_model                         small
% 3.62/1.05  --sat_out_clauses                       false
% 3.62/1.05  
% 3.62/1.05  ------ QBF Options
% 3.62/1.05  
% 3.62/1.05  --qbf_mode                              false
% 3.62/1.05  --qbf_elim_univ                         false
% 3.62/1.05  --qbf_dom_inst                          none
% 3.62/1.05  --qbf_dom_pre_inst                      false
% 3.62/1.05  --qbf_sk_in                             false
% 3.62/1.05  --qbf_pred_elim                         true
% 3.62/1.05  --qbf_split                             512
% 3.62/1.05  
% 3.62/1.05  ------ BMC1 Options
% 3.62/1.05  
% 3.62/1.05  --bmc1_incremental                      false
% 3.62/1.05  --bmc1_axioms                           reachable_all
% 3.62/1.05  --bmc1_min_bound                        0
% 3.62/1.05  --bmc1_max_bound                        -1
% 3.62/1.05  --bmc1_max_bound_default                -1
% 3.62/1.05  --bmc1_symbol_reachability              true
% 3.62/1.05  --bmc1_property_lemmas                  false
% 3.62/1.05  --bmc1_k_induction                      false
% 3.62/1.05  --bmc1_non_equiv_states                 false
% 3.62/1.05  --bmc1_deadlock                         false
% 3.62/1.05  --bmc1_ucm                              false
% 3.62/1.05  --bmc1_add_unsat_core                   none
% 3.62/1.05  --bmc1_unsat_core_children              false
% 3.62/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.05  --bmc1_out_stat                         full
% 3.62/1.05  --bmc1_ground_init                      false
% 3.62/1.05  --bmc1_pre_inst_next_state              false
% 3.62/1.05  --bmc1_pre_inst_state                   false
% 3.62/1.05  --bmc1_pre_inst_reach_state             false
% 3.62/1.05  --bmc1_out_unsat_core                   false
% 3.62/1.05  --bmc1_aig_witness_out                  false
% 3.62/1.05  --bmc1_verbose                          false
% 3.62/1.05  --bmc1_dump_clauses_tptp                false
% 3.62/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.05  --bmc1_dump_file                        -
% 3.62/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.05  --bmc1_ucm_extend_mode                  1
% 3.62/1.05  --bmc1_ucm_init_mode                    2
% 3.62/1.05  --bmc1_ucm_cone_mode                    none
% 3.62/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.05  --bmc1_ucm_relax_model                  4
% 3.62/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.05  --bmc1_ucm_layered_model                none
% 3.62/1.05  --bmc1_ucm_max_lemma_size               10
% 3.62/1.05  
% 3.62/1.05  ------ AIG Options
% 3.62/1.05  
% 3.62/1.05  --aig_mode                              false
% 3.62/1.05  
% 3.62/1.05  ------ Instantiation Options
% 3.62/1.05  
% 3.62/1.05  --instantiation_flag                    true
% 3.62/1.05  --inst_sos_flag                         false
% 3.62/1.05  --inst_sos_phase                        true
% 3.62/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel_side                     num_symb
% 3.62/1.05  --inst_solver_per_active                1400
% 3.62/1.05  --inst_solver_calls_frac                1.
% 3.62/1.05  --inst_passive_queue_type               priority_queues
% 3.62/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.05  --inst_passive_queues_freq              [25;2]
% 3.62/1.05  --inst_dismatching                      true
% 3.62/1.05  --inst_eager_unprocessed_to_passive     true
% 3.62/1.05  --inst_prop_sim_given                   true
% 3.62/1.05  --inst_prop_sim_new                     false
% 3.62/1.05  --inst_subs_new                         false
% 3.62/1.05  --inst_eq_res_simp                      false
% 3.62/1.05  --inst_subs_given                       false
% 3.62/1.05  --inst_orphan_elimination               true
% 3.62/1.05  --inst_learning_loop_flag               true
% 3.62/1.05  --inst_learning_start                   3000
% 3.62/1.05  --inst_learning_factor                  2
% 3.62/1.05  --inst_start_prop_sim_after_learn       3
% 3.62/1.05  --inst_sel_renew                        solver
% 3.62/1.05  --inst_lit_activity_flag                true
% 3.62/1.05  --inst_restr_to_given                   false
% 3.62/1.05  --inst_activity_threshold               500
% 3.62/1.05  --inst_out_proof                        true
% 3.62/1.05  
% 3.62/1.05  ------ Resolution Options
% 3.62/1.05  
% 3.62/1.05  --resolution_flag                       true
% 3.62/1.05  --res_lit_sel                           adaptive
% 3.62/1.05  --res_lit_sel_side                      none
% 3.62/1.05  --res_ordering                          kbo
% 3.62/1.05  --res_to_prop_solver                    active
% 3.62/1.05  --res_prop_simpl_new                    false
% 3.62/1.05  --res_prop_simpl_given                  true
% 3.62/1.05  --res_passive_queue_type                priority_queues
% 3.62/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.05  --res_passive_queues_freq               [15;5]
% 3.62/1.05  --res_forward_subs                      full
% 3.62/1.05  --res_backward_subs                     full
% 3.62/1.05  --res_forward_subs_resolution           true
% 3.62/1.05  --res_backward_subs_resolution          true
% 3.62/1.05  --res_orphan_elimination                true
% 3.62/1.05  --res_time_limit                        2.
% 3.62/1.05  --res_out_proof                         true
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Options
% 3.62/1.05  
% 3.62/1.05  --superposition_flag                    true
% 3.62/1.05  --sup_passive_queue_type                priority_queues
% 3.62/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.05  --demod_completeness_check              fast
% 3.62/1.05  --demod_use_ground                      true
% 3.62/1.05  --sup_to_prop_solver                    passive
% 3.62/1.05  --sup_prop_simpl_new                    true
% 3.62/1.05  --sup_prop_simpl_given                  true
% 3.62/1.05  --sup_fun_splitting                     false
% 3.62/1.05  --sup_smt_interval                      50000
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Simplification Setup
% 3.62/1.05  
% 3.62/1.05  --sup_indices_passive                   []
% 3.62/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_full_bw                           [BwDemod]
% 3.62/1.05  --sup_immed_triv                        [TrivRules]
% 3.62/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_immed_bw_main                     []
% 3.62/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  
% 3.62/1.05  ------ Combination Options
% 3.62/1.05  
% 3.62/1.05  --comb_res_mult                         3
% 3.62/1.05  --comb_sup_mult                         2
% 3.62/1.05  --comb_inst_mult                        10
% 3.62/1.05  
% 3.62/1.05  ------ Debug Options
% 3.62/1.05  
% 3.62/1.05  --dbg_backtrace                         false
% 3.62/1.05  --dbg_dump_prop_clauses                 false
% 3.62/1.05  --dbg_dump_prop_clauses_file            -
% 3.62/1.05  --dbg_out_stat                          false
% 3.62/1.05  ------ Parsing...
% 3.62/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/1.05  ------ Proving...
% 3.62/1.05  ------ Problem Properties 
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  clauses                                 34
% 3.62/1.05  conjectures                             6
% 3.62/1.05  EPR                                     9
% 3.62/1.05  Horn                                    11
% 3.62/1.05  unary                                   2
% 3.62/1.05  binary                                  9
% 3.62/1.05  lits                                    169
% 3.62/1.05  lits eq                                 6
% 3.62/1.05  fd_pure                                 0
% 3.62/1.05  fd_pseudo                               0
% 3.62/1.05  fd_cond                                 0
% 3.62/1.05  fd_pseudo_cond                          4
% 3.62/1.05  AC symbols                              0
% 3.62/1.05  
% 3.62/1.05  ------ Schedule dynamic 5 is on 
% 3.62/1.05  
% 3.62/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  ------ 
% 3.62/1.05  Current options:
% 3.62/1.05  ------ 
% 3.62/1.05  
% 3.62/1.05  ------ Input Options
% 3.62/1.05  
% 3.62/1.05  --out_options                           all
% 3.62/1.05  --tptp_safe_out                         true
% 3.62/1.05  --problem_path                          ""
% 3.62/1.05  --include_path                          ""
% 3.62/1.05  --clausifier                            res/vclausify_rel
% 3.62/1.05  --clausifier_options                    --mode clausify
% 3.62/1.05  --stdin                                 false
% 3.62/1.05  --stats_out                             all
% 3.62/1.05  
% 3.62/1.05  ------ General Options
% 3.62/1.05  
% 3.62/1.05  --fof                                   false
% 3.62/1.05  --time_out_real                         305.
% 3.62/1.05  --time_out_virtual                      -1.
% 3.62/1.05  --symbol_type_check                     false
% 3.62/1.05  --clausify_out                          false
% 3.62/1.05  --sig_cnt_out                           false
% 3.62/1.05  --trig_cnt_out                          false
% 3.62/1.05  --trig_cnt_out_tolerance                1.
% 3.62/1.05  --trig_cnt_out_sk_spl                   false
% 3.62/1.05  --abstr_cl_out                          false
% 3.62/1.05  
% 3.62/1.05  ------ Global Options
% 3.62/1.05  
% 3.62/1.05  --schedule                              default
% 3.62/1.05  --add_important_lit                     false
% 3.62/1.05  --prop_solver_per_cl                    1000
% 3.62/1.05  --min_unsat_core                        false
% 3.62/1.05  --soft_assumptions                      false
% 3.62/1.05  --soft_lemma_size                       3
% 3.62/1.05  --prop_impl_unit_size                   0
% 3.62/1.05  --prop_impl_unit                        []
% 3.62/1.05  --share_sel_clauses                     true
% 3.62/1.05  --reset_solvers                         false
% 3.62/1.05  --bc_imp_inh                            [conj_cone]
% 3.62/1.05  --conj_cone_tolerance                   3.
% 3.62/1.05  --extra_neg_conj                        none
% 3.62/1.05  --large_theory_mode                     true
% 3.62/1.05  --prolific_symb_bound                   200
% 3.62/1.05  --lt_threshold                          2000
% 3.62/1.05  --clause_weak_htbl                      true
% 3.62/1.05  --gc_record_bc_elim                     false
% 3.62/1.05  
% 3.62/1.05  ------ Preprocessing Options
% 3.62/1.05  
% 3.62/1.05  --preprocessing_flag                    true
% 3.62/1.05  --time_out_prep_mult                    0.1
% 3.62/1.05  --splitting_mode                        input
% 3.62/1.05  --splitting_grd                         true
% 3.62/1.05  --splitting_cvd                         false
% 3.62/1.05  --splitting_cvd_svl                     false
% 3.62/1.05  --splitting_nvd                         32
% 3.62/1.05  --sub_typing                            true
% 3.62/1.05  --prep_gs_sim                           true
% 3.62/1.05  --prep_unflatten                        true
% 3.62/1.05  --prep_res_sim                          true
% 3.62/1.05  --prep_upred                            true
% 3.62/1.05  --prep_sem_filter                       exhaustive
% 3.62/1.05  --prep_sem_filter_out                   false
% 3.62/1.05  --pred_elim                             true
% 3.62/1.05  --res_sim_input                         true
% 3.62/1.05  --eq_ax_congr_red                       true
% 3.62/1.05  --pure_diseq_elim                       true
% 3.62/1.05  --brand_transform                       false
% 3.62/1.05  --non_eq_to_eq                          false
% 3.62/1.05  --prep_def_merge                        true
% 3.62/1.05  --prep_def_merge_prop_impl              false
% 3.62/1.05  --prep_def_merge_mbd                    true
% 3.62/1.05  --prep_def_merge_tr_red                 false
% 3.62/1.05  --prep_def_merge_tr_cl                  false
% 3.62/1.05  --smt_preprocessing                     true
% 3.62/1.05  --smt_ac_axioms                         fast
% 3.62/1.05  --preprocessed_out                      false
% 3.62/1.05  --preprocessed_stats                    false
% 3.62/1.05  
% 3.62/1.05  ------ Abstraction refinement Options
% 3.62/1.05  
% 3.62/1.05  --abstr_ref                             []
% 3.62/1.05  --abstr_ref_prep                        false
% 3.62/1.05  --abstr_ref_until_sat                   false
% 3.62/1.05  --abstr_ref_sig_restrict                funpre
% 3.62/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.62/1.05  --abstr_ref_under                       []
% 3.62/1.05  
% 3.62/1.05  ------ SAT Options
% 3.62/1.05  
% 3.62/1.05  --sat_mode                              false
% 3.62/1.05  --sat_fm_restart_options                ""
% 3.62/1.05  --sat_gr_def                            false
% 3.62/1.05  --sat_epr_types                         true
% 3.62/1.05  --sat_non_cyclic_types                  false
% 3.62/1.05  --sat_finite_models                     false
% 3.62/1.05  --sat_fm_lemmas                         false
% 3.62/1.05  --sat_fm_prep                           false
% 3.62/1.05  --sat_fm_uc_incr                        true
% 3.62/1.05  --sat_out_model                         small
% 3.62/1.05  --sat_out_clauses                       false
% 3.62/1.05  
% 3.62/1.05  ------ QBF Options
% 3.62/1.05  
% 3.62/1.05  --qbf_mode                              false
% 3.62/1.05  --qbf_elim_univ                         false
% 3.62/1.05  --qbf_dom_inst                          none
% 3.62/1.05  --qbf_dom_pre_inst                      false
% 3.62/1.05  --qbf_sk_in                             false
% 3.62/1.05  --qbf_pred_elim                         true
% 3.62/1.05  --qbf_split                             512
% 3.62/1.05  
% 3.62/1.05  ------ BMC1 Options
% 3.62/1.05  
% 3.62/1.05  --bmc1_incremental                      false
% 3.62/1.05  --bmc1_axioms                           reachable_all
% 3.62/1.05  --bmc1_min_bound                        0
% 3.62/1.05  --bmc1_max_bound                        -1
% 3.62/1.05  --bmc1_max_bound_default                -1
% 3.62/1.05  --bmc1_symbol_reachability              true
% 3.62/1.05  --bmc1_property_lemmas                  false
% 3.62/1.05  --bmc1_k_induction                      false
% 3.62/1.05  --bmc1_non_equiv_states                 false
% 3.62/1.05  --bmc1_deadlock                         false
% 3.62/1.05  --bmc1_ucm                              false
% 3.62/1.05  --bmc1_add_unsat_core                   none
% 3.62/1.05  --bmc1_unsat_core_children              false
% 3.62/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.62/1.05  --bmc1_out_stat                         full
% 3.62/1.05  --bmc1_ground_init                      false
% 3.62/1.05  --bmc1_pre_inst_next_state              false
% 3.62/1.05  --bmc1_pre_inst_state                   false
% 3.62/1.05  --bmc1_pre_inst_reach_state             false
% 3.62/1.05  --bmc1_out_unsat_core                   false
% 3.62/1.05  --bmc1_aig_witness_out                  false
% 3.62/1.05  --bmc1_verbose                          false
% 3.62/1.05  --bmc1_dump_clauses_tptp                false
% 3.62/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.62/1.05  --bmc1_dump_file                        -
% 3.62/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.62/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.62/1.05  --bmc1_ucm_extend_mode                  1
% 3.62/1.05  --bmc1_ucm_init_mode                    2
% 3.62/1.05  --bmc1_ucm_cone_mode                    none
% 3.62/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.62/1.05  --bmc1_ucm_relax_model                  4
% 3.62/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.62/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.62/1.05  --bmc1_ucm_layered_model                none
% 3.62/1.05  --bmc1_ucm_max_lemma_size               10
% 3.62/1.05  
% 3.62/1.05  ------ AIG Options
% 3.62/1.05  
% 3.62/1.05  --aig_mode                              false
% 3.62/1.05  
% 3.62/1.05  ------ Instantiation Options
% 3.62/1.05  
% 3.62/1.05  --instantiation_flag                    true
% 3.62/1.05  --inst_sos_flag                         false
% 3.62/1.05  --inst_sos_phase                        true
% 3.62/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.62/1.05  --inst_lit_sel_side                     none
% 3.62/1.05  --inst_solver_per_active                1400
% 3.62/1.05  --inst_solver_calls_frac                1.
% 3.62/1.05  --inst_passive_queue_type               priority_queues
% 3.62/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.62/1.05  --inst_passive_queues_freq              [25;2]
% 3.62/1.05  --inst_dismatching                      true
% 3.62/1.05  --inst_eager_unprocessed_to_passive     true
% 3.62/1.05  --inst_prop_sim_given                   true
% 3.62/1.05  --inst_prop_sim_new                     false
% 3.62/1.05  --inst_subs_new                         false
% 3.62/1.05  --inst_eq_res_simp                      false
% 3.62/1.05  --inst_subs_given                       false
% 3.62/1.05  --inst_orphan_elimination               true
% 3.62/1.05  --inst_learning_loop_flag               true
% 3.62/1.05  --inst_learning_start                   3000
% 3.62/1.05  --inst_learning_factor                  2
% 3.62/1.05  --inst_start_prop_sim_after_learn       3
% 3.62/1.05  --inst_sel_renew                        solver
% 3.62/1.05  --inst_lit_activity_flag                true
% 3.62/1.05  --inst_restr_to_given                   false
% 3.62/1.05  --inst_activity_threshold               500
% 3.62/1.05  --inst_out_proof                        true
% 3.62/1.05  
% 3.62/1.05  ------ Resolution Options
% 3.62/1.05  
% 3.62/1.05  --resolution_flag                       false
% 3.62/1.05  --res_lit_sel                           adaptive
% 3.62/1.05  --res_lit_sel_side                      none
% 3.62/1.05  --res_ordering                          kbo
% 3.62/1.05  --res_to_prop_solver                    active
% 3.62/1.05  --res_prop_simpl_new                    false
% 3.62/1.05  --res_prop_simpl_given                  true
% 3.62/1.05  --res_passive_queue_type                priority_queues
% 3.62/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.62/1.05  --res_passive_queues_freq               [15;5]
% 3.62/1.05  --res_forward_subs                      full
% 3.62/1.05  --res_backward_subs                     full
% 3.62/1.05  --res_forward_subs_resolution           true
% 3.62/1.05  --res_backward_subs_resolution          true
% 3.62/1.05  --res_orphan_elimination                true
% 3.62/1.05  --res_time_limit                        2.
% 3.62/1.05  --res_out_proof                         true
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Options
% 3.62/1.05  
% 3.62/1.05  --superposition_flag                    true
% 3.62/1.05  --sup_passive_queue_type                priority_queues
% 3.62/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.62/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.62/1.05  --demod_completeness_check              fast
% 3.62/1.05  --demod_use_ground                      true
% 3.62/1.05  --sup_to_prop_solver                    passive
% 3.62/1.05  --sup_prop_simpl_new                    true
% 3.62/1.05  --sup_prop_simpl_given                  true
% 3.62/1.05  --sup_fun_splitting                     false
% 3.62/1.05  --sup_smt_interval                      50000
% 3.62/1.05  
% 3.62/1.05  ------ Superposition Simplification Setup
% 3.62/1.05  
% 3.62/1.05  --sup_indices_passive                   []
% 3.62/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.62/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.62/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_full_bw                           [BwDemod]
% 3.62/1.05  --sup_immed_triv                        [TrivRules]
% 3.62/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.62/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_immed_bw_main                     []
% 3.62/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.62/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.62/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.62/1.05  
% 3.62/1.05  ------ Combination Options
% 3.62/1.05  
% 3.62/1.05  --comb_res_mult                         3
% 3.62/1.05  --comb_sup_mult                         2
% 3.62/1.05  --comb_inst_mult                        10
% 3.62/1.05  
% 3.62/1.05  ------ Debug Options
% 3.62/1.05  
% 3.62/1.05  --dbg_backtrace                         false
% 3.62/1.05  --dbg_dump_prop_clauses                 false
% 3.62/1.05  --dbg_dump_prop_clauses_file            -
% 3.62/1.05  --dbg_out_stat                          false
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  ------ Proving...
% 3.62/1.05  
% 3.62/1.05  
% 3.62/1.05  % SZS status Theorem for theBenchmark.p
% 3.62/1.05  
% 3.62/1.05   Resolution empty clause
% 3.62/1.05  
% 3.62/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/1.05  
% 3.62/1.05  fof(f14,conjecture,(
% 3.62/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f15,negated_conjecture,(
% 3.62/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.62/1.05    inference(negated_conjecture,[],[f14])).
% 3.62/1.05  
% 3.62/1.05  fof(f38,plain,(
% 3.62/1.05    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f15])).
% 3.62/1.05  
% 3.62/1.05  fof(f39,plain,(
% 3.62/1.05    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f38])).
% 3.62/1.05  
% 3.62/1.05  fof(f55,plain,(
% 3.62/1.05    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.05    inference(nnf_transformation,[],[f39])).
% 3.62/1.05  
% 3.62/1.05  fof(f56,plain,(
% 3.62/1.05    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f55])).
% 3.62/1.05  
% 3.62/1.05  fof(f57,plain,(
% 3.62/1.05    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/1.05    inference(rectify,[],[f56])).
% 3.62/1.05  
% 3.62/1.05  fof(f60,plain,(
% 3.62/1.05    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK8(X3),X0) & m2_yellow_6(sK8(X3),X0,X3)))) )),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f59,plain,(
% 3.62/1.05    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK7)) & l1_waybel_0(sK7,X0) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7))) )),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f58,plain,(
% 3.62/1.05    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,X1)) & l1_waybel_0(X1,sK6) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK6)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK6) & m2_yellow_6(X4,sK6,X3)) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK6)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f61,plain,(
% 3.62/1.05    ((! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,sK7)) & l1_waybel_0(sK7,sK6) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7)) | ~v1_compts_1(sK6)) & (! [X3] : ((v3_yellow_6(sK8(X3),sK6) & m2_yellow_6(sK8(X3),sK6,X3)) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK6)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 3.62/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f57,f60,f59,f58])).
% 3.62/1.05  
% 3.62/1.05  fof(f95,plain,(
% 3.62/1.05    ( ! [X3] : (m2_yellow_6(sK8(X3),sK6,X3) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK6)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f6,axiom,(
% 3.62/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f22,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f6])).
% 3.62/1.05  
% 3.62/1.05  fof(f23,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f22])).
% 3.62/1.05  
% 3.62/1.05  fof(f40,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(nnf_transformation,[],[f23])).
% 3.62/1.05  
% 3.62/1.05  fof(f41,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f40])).
% 3.62/1.05  
% 3.62/1.05  fof(f42,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(rectify,[],[f41])).
% 3.62/1.05  
% 3.62/1.05  fof(f45,plain,(
% 3.62/1.05    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6)))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f44,plain,(
% 3.62/1.05    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X3)))) )),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f43,plain,(
% 3.62/1.05    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f46,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f45,f44,f43])).
% 3.62/1.05  
% 3.62/1.05  fof(f70,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f46])).
% 3.62/1.05  
% 3.62/1.05  fof(f93,plain,(
% 3.62/1.05    v2_pre_topc(sK6)),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f92,plain,(
% 3.62/1.05    ~v2_struct_0(sK6)),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f94,plain,(
% 3.62/1.05    l1_pre_topc(sK6)),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f7,axiom,(
% 3.62/1.05    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f24,plain,(
% 3.62/1.05    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f7])).
% 3.62/1.05  
% 3.62/1.05  fof(f25,plain,(
% 3.62/1.05    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f24])).
% 3.62/1.05  
% 3.62/1.05  fof(f74,plain,(
% 3.62/1.05    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f25])).
% 3.62/1.05  
% 3.62/1.05  fof(f68,plain,(
% 3.62/1.05    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f46])).
% 3.62/1.05  
% 3.62/1.05  fof(f103,plain,(
% 3.62/1.05    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(equality_resolution,[],[f68])).
% 3.62/1.05  
% 3.62/1.05  fof(f71,plain,(
% 3.62/1.05    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2)) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f46])).
% 3.62/1.05  
% 3.62/1.05  fof(f1,axiom,(
% 3.62/1.05    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f62,plain,(
% 3.62/1.05    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.62/1.05    inference(cnf_transformation,[],[f1])).
% 3.62/1.05  
% 3.62/1.05  fof(f2,axiom,(
% 3.62/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f16,plain,(
% 3.62/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 3.62/1.05    inference(unused_predicate_definition_removal,[],[f2])).
% 3.62/1.05  
% 3.62/1.05  fof(f17,plain,(
% 3.62/1.05    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.62/1.05    inference(ennf_transformation,[],[f16])).
% 3.62/1.05  
% 3.62/1.05  fof(f63,plain,(
% 3.62/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.62/1.05    inference(cnf_transformation,[],[f17])).
% 3.62/1.05  
% 3.62/1.05  fof(f4,axiom,(
% 3.62/1.05    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f20,plain,(
% 3.62/1.05    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.62/1.05    inference(ennf_transformation,[],[f4])).
% 3.62/1.05  
% 3.62/1.05  fof(f65,plain,(
% 3.62/1.05    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f20])).
% 3.62/1.05  
% 3.62/1.05  fof(f69,plain,(
% 3.62/1.05    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f46])).
% 3.62/1.05  
% 3.62/1.05  fof(f102,plain,(
% 3.62/1.05    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(equality_resolution,[],[f69])).
% 3.62/1.05  
% 3.62/1.05  fof(f10,axiom,(
% 3.62/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f30,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f10])).
% 3.62/1.05  
% 3.62/1.05  fof(f31,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f30])).
% 3.62/1.05  
% 3.62/1.05  fof(f81,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f31])).
% 3.62/1.05  
% 3.62/1.05  fof(f3,axiom,(
% 3.62/1.05    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f18,plain,(
% 3.62/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.62/1.05    inference(ennf_transformation,[],[f3])).
% 3.62/1.05  
% 3.62/1.05  fof(f19,plain,(
% 3.62/1.05    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.62/1.05    inference(flattening,[],[f18])).
% 3.62/1.05  
% 3.62/1.05  fof(f64,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f19])).
% 3.62/1.05  
% 3.62/1.05  fof(f11,axiom,(
% 3.62/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f32,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f11])).
% 3.62/1.05  
% 3.62/1.05  fof(f33,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f32])).
% 3.62/1.05  
% 3.62/1.05  fof(f82,plain,(
% 3.62/1.05    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f33])).
% 3.62/1.05  
% 3.62/1.05  fof(f5,axiom,(
% 3.62/1.05    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f21,plain,(
% 3.62/1.05    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.62/1.05    inference(ennf_transformation,[],[f5])).
% 3.62/1.05  
% 3.62/1.05  fof(f66,plain,(
% 3.62/1.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f21])).
% 3.62/1.05  
% 3.62/1.05  fof(f8,axiom,(
% 3.62/1.05    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f26,plain,(
% 3.62/1.05    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f8])).
% 3.62/1.05  
% 3.62/1.05  fof(f27,plain,(
% 3.62/1.05    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f26])).
% 3.62/1.05  
% 3.62/1.05  fof(f78,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f27])).
% 3.62/1.05  
% 3.62/1.05  fof(f77,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f27])).
% 3.62/1.05  
% 3.62/1.05  fof(f76,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f27])).
% 3.62/1.05  
% 3.62/1.05  fof(f75,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f27])).
% 3.62/1.05  
% 3.62/1.05  fof(f13,axiom,(
% 3.62/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f36,plain,(
% 3.62/1.05    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f13])).
% 3.62/1.05  
% 3.62/1.05  fof(f37,plain,(
% 3.62/1.05    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f36])).
% 3.62/1.05  
% 3.62/1.05  fof(f50,plain,(
% 3.62/1.05    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(nnf_transformation,[],[f37])).
% 3.62/1.05  
% 3.62/1.05  fof(f51,plain,(
% 3.62/1.05    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(rectify,[],[f50])).
% 3.62/1.05  
% 3.62/1.05  fof(f53,plain,(
% 3.62/1.05    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f52,plain,(
% 3.62/1.05    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f54,plain,(
% 3.62/1.05    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f51,f53,f52])).
% 3.62/1.05  
% 3.62/1.05  fof(f91,plain,(
% 3.62/1.05    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f54])).
% 3.62/1.05  
% 3.62/1.05  fof(f87,plain,(
% 3.62/1.05    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f54])).
% 3.62/1.05  
% 3.62/1.05  fof(f88,plain,(
% 3.62/1.05    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f54])).
% 3.62/1.05  
% 3.62/1.05  fof(f89,plain,(
% 3.62/1.05    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f54])).
% 3.62/1.05  
% 3.62/1.05  fof(f90,plain,(
% 3.62/1.05    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK4(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f54])).
% 3.62/1.05  
% 3.62/1.05  fof(f9,axiom,(
% 3.62/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f28,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f9])).
% 3.62/1.05  
% 3.62/1.05  fof(f29,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f28])).
% 3.62/1.05  
% 3.62/1.05  fof(f47,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(nnf_transformation,[],[f29])).
% 3.62/1.05  
% 3.62/1.05  fof(f79,plain,(
% 3.62/1.05    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f47])).
% 3.62/1.05  
% 3.62/1.05  fof(f96,plain,(
% 3.62/1.05    ( ! [X3] : (v3_yellow_6(sK8(X3),sK6) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK6)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f86,plain,(
% 3.62/1.05    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK5(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f54])).
% 3.62/1.05  
% 3.62/1.05  fof(f12,axiom,(
% 3.62/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.62/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/1.05  
% 3.62/1.05  fof(f34,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/1.05    inference(ennf_transformation,[],[f12])).
% 3.62/1.05  
% 3.62/1.05  fof(f35,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(flattening,[],[f34])).
% 3.62/1.05  
% 3.62/1.05  fof(f48,plain,(
% 3.62/1.05    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)))),
% 3.62/1.05    introduced(choice_axiom,[])).
% 3.62/1.05  
% 3.62/1.05  fof(f49,plain,(
% 3.62/1.05    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f48])).
% 3.62/1.05  
% 3.62/1.05  fof(f83,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (m2_yellow_6(sK3(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f49])).
% 3.62/1.05  
% 3.62/1.05  fof(f80,plain,(
% 3.62/1.05    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f47])).
% 3.62/1.05  
% 3.62/1.05  fof(f101,plain,(
% 3.62/1.05    ( ! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,sK7) | ~v1_compts_1(sK6)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f97,plain,(
% 3.62/1.05    ~v2_struct_0(sK7) | ~v1_compts_1(sK6)),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f98,plain,(
% 3.62/1.05    v4_orders_2(sK7) | ~v1_compts_1(sK6)),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f99,plain,(
% 3.62/1.05    v7_waybel_0(sK7) | ~v1_compts_1(sK6)),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f100,plain,(
% 3.62/1.05    l1_waybel_0(sK7,sK6) | ~v1_compts_1(sK6)),
% 3.62/1.05    inference(cnf_transformation,[],[f61])).
% 3.62/1.05  
% 3.62/1.05  fof(f85,plain,(
% 3.62/1.05    ( ! [X0,X3] : (m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f54])).
% 3.62/1.05  
% 3.62/1.05  fof(f84,plain,(
% 3.62/1.05    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/1.05    inference(cnf_transformation,[],[f49])).
% 3.62/1.05  
% 3.62/1.05  cnf(c_36,negated_conjecture,
% 3.62/1.05      ( m2_yellow_6(sK8(X0),sK6,X0)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f95]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8707,plain,
% 3.62/1.05      ( m2_yellow_6(sK8(X0),sK6,X0) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 3.62/1.05      | ~ v2_pre_topc(X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k10_yellow_6(X1,X0) = X2 ),
% 3.62/1.05      inference(cnf_transformation,[],[f70]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_38,negated_conjecture,
% 3.62/1.05      ( v2_pre_topc(sK6) ),
% 3.62/1.05      inference(cnf_transformation,[],[f93]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1612,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k10_yellow_6(X1,X0) = X2
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_8,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1613,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = X1 ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1612]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_39,negated_conjecture,
% 3.62/1.05      ( ~ v2_struct_0(sK6) ),
% 3.62/1.05      inference(cnf_transformation,[],[f92]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_37,negated_conjecture,
% 3.62/1.05      ( l1_pre_topc(sK6) ),
% 3.62/1.05      inference(cnf_transformation,[],[f94]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1617,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = X1 ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1613,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1618,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = X1 ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1617]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8686,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = X1
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6)) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1618]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ v2_pre_topc(X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f74]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1537,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_12,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1538,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1537]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1542,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1538,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1543,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1542]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10,plain,
% 3.62/1.05      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f103]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1363,plain,
% 3.62/1.05      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_10,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1364,plain,
% 3.62/1.05      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1363]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1368,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1364,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1369,plain,
% 3.62/1.05      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1368]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1560,plain,
% 3.62/1.05      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(backward_subsumption_resolution,[status(thm)],[c_1543,c_1369]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8689,plain,
% 3.62/1.05      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0)) = iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1560]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_7,plain,
% 3.62/1.05      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 3.62/1.05      | r1_waybel_0(X1,X2,X0)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | r2_hidden(sK0(X1,X2,X3),X3)
% 3.62/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | ~ v2_pre_topc(X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k10_yellow_6(X1,X2) = X3 ),
% 3.62/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1645,plain,
% 3.62/1.05      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 3.62/1.05      | r1_waybel_0(X1,X2,X0)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | r2_hidden(sK0(X1,X2,X3),X3)
% 3.62/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k10_yellow_6(X1,X2) = X3
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_7,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1646,plain,
% 3.62/1.05      ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.62/1.05      | r1_waybel_0(sK6,X1,X0)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(sK6)
% 3.62/1.05      | k10_yellow_6(sK6,X1) = X2 ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1645]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1650,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.62/1.05      | r1_waybel_0(sK6,X1,X0)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | k10_yellow_6(sK6,X1) = X2 ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1646,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1651,plain,
% 3.62/1.05      ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.62/1.05      | r1_waybel_0(sK6,X1,X0)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | k10_yellow_6(sK6,X1) = X2 ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1650]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8685,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = X1
% 3.62/1.05      | m1_connsp_2(X2,sK6,sK0(sK6,X0,X1)) != iProver_top
% 3.62/1.05      | r1_waybel_0(sK6,X0,X2) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11342,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = X1
% 3.62/1.05      | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
% 3.62/1.05      | l1_waybel_0(X2,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X2) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X2) != iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X2) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8689,c_8685]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2155,plain,
% 3.62/1.05      ( r1_waybel_0(sK6,X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X2,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X3,k10_yellow_6(sK6,X2))
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X4),X4)
% 3.62/1.05      | ~ m1_subset_1(X3,u1_struct_0(sK6))
% 3.62/1.05      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | sK2(sK6,X2,X3) != X1
% 3.62/1.05      | sK0(sK6,X0,X4) != X3
% 3.62/1.05      | k10_yellow_6(sK6,X0) = X4
% 3.62/1.05      | sK6 != sK6 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_1560,c_1651]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2156,plain,
% 3.62/1.05      ( r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,X2)))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X2),X2)
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X2),k10_yellow_6(sK6,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | ~ m1_subset_1(sK0(sK6,X0,X2),u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = X2 ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_2155]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2188,plain,
% 3.62/1.05      ( r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,X2)))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X2),X2)
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X2),k10_yellow_6(sK6,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = X2 ),
% 3.62/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_2156,c_1618]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2202,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = X1
% 3.62/1.05      | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X2,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(X2) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v4_orders_2(X2) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X2) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_2188]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11920,plain,
% 3.62/1.05      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X2,sK6) != iProver_top
% 3.62/1.05      | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,X0) = X1
% 3.62/1.05      | v2_struct_0(X2) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X2) != iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X2) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_11342,c_2202]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11921,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = X1
% 3.62/1.05      | r1_waybel_0(sK6,X0,sK2(sK6,X2,sK0(sK6,X0,X1))) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X2,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),X1) = iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,X1),k10_yellow_6(sK6,X2)) = iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(X2) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v4_orders_2(X2) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X2) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_11920]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_0,plain,
% 3.62/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.62/1.05      inference(cnf_transformation,[],[f62]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8713,plain,
% 3.62/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1,plain,
% 3.62/1.05      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.62/1.05      inference(cnf_transformation,[],[f63]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_3,plain,
% 3.62/1.05      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f65]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_442,plain,
% 3.62/1.05      ( ~ r2_hidden(X0,X1)
% 3.62/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.62/1.05      | X1 != X2
% 3.62/1.05      | X0 != X3 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_443,plain,
% 3.62/1.05      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_442]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8705,plain,
% 3.62/1.05      ( r2_hidden(X0,X1) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9307,plain,
% 3.62/1.05      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8713,c_8705]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11940,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,k1_xboole_0))) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X1)) = iProver_top
% 3.62/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_11921,c_9307]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9421,plain,
% 3.62/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9424,plain,
% 3.62/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9421]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12518,plain,
% 3.62/1.05      ( r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X1)) = iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,k1_xboole_0))) = iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_11940,c_9424]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12519,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r1_waybel_0(sK6,X0,sK2(sK6,X1,sK0(sK6,X0,k1_xboole_0))) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X1)) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_12518]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9,plain,
% 3.62/1.05      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f102]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1399,plain,
% 3.62/1.05      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_9,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1400,plain,
% 3.62/1.05      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1399]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1404,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1400,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1405,plain,
% 3.62/1.05      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1404]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1561,plain,
% 3.62/1.05      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(backward_subsumption_resolution,[status(thm)],[c_1543,c_1405]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8688,plain,
% 3.62/1.05      ( r1_waybel_0(sK6,X0,sK2(sK6,X0,X1)) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0)) = iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12535,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(sK0(sK6,X0,k1_xboole_0),k10_yellow_6(sK6,X0)) = iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_12519,c_8688]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_19,plain,
% 3.62/1.05      ( r3_waybel_9(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f81]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1330,plain,
% 3.62/1.05      ( r3_waybel_9(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1331,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1330]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1335,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1331,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1336,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1335]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8694,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1336]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1337,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1336]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8690,plain,
% 3.62/1.05      ( l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1543]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2,plain,
% 3.62/1.05      ( ~ r2_hidden(X0,X1)
% 3.62/1.05      | m1_subset_1(X0,X2)
% 3.62/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.62/1.05      inference(cnf_transformation,[],[f64]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8712,plain,
% 3.62/1.05      ( r2_hidden(X0,X1) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,X2) = iProver_top
% 3.62/1.05      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9531,plain,
% 3.62/1.05      ( l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8690,c_8712]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10344,plain,
% 3.62/1.05      ( r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r3_waybel_9(sK6,X0,X1) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_8694,c_1337,c_9531]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10345,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r2_hidden(X1,k10_yellow_6(sK6,X0)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_10344]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12692,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_12535,c_10345]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12795,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8686,c_12692]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12800,plain,
% 3.62/1.05      ( l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_12795,c_9424]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12801,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X0,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_12800]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_20,plain,
% 3.62/1.05      ( ~ r3_waybel_9(X0,X1,X2)
% 3.62/1.05      | r3_waybel_9(X0,X3,X2)
% 3.62/1.05      | ~ m2_yellow_6(X1,X0,X3)
% 3.62/1.05      | ~ l1_waybel_0(X3,X0)
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X3)
% 3.62/1.05      | ~ v4_orders_2(X3)
% 3.62/1.05      | ~ v7_waybel_0(X3)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f82]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1298,plain,
% 3.62/1.05      ( ~ r3_waybel_9(X0,X1,X2)
% 3.62/1.05      | r3_waybel_9(X0,X3,X2)
% 3.62/1.05      | ~ m2_yellow_6(X1,X0,X3)
% 3.62/1.05      | ~ l1_waybel_0(X3,X0)
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X3)
% 3.62/1.05      | ~ v4_orders_2(X3)
% 3.62/1.05      | ~ v7_waybel_0(X3)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_20,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1299,plain,
% 3.62/1.05      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | r3_waybel_9(sK6,X2,X1)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1298]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1301,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | r3_waybel_9(sK6,X2,X1)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X2) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1299,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1302,plain,
% 3.62/1.05      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | r3_waybel_9(sK6,X2,X1)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1301]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8695,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1) != iProver_top
% 3.62/1.05      | r3_waybel_9(sK6,X2,X1) = iProver_top
% 3.62/1.05      | m2_yellow_6(X0,sK6,X2) != iProver_top
% 3.62/1.05      | l1_waybel_0(X2,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X2) = iProver_top
% 3.62/1.05      | v4_orders_2(X2) != iProver_top
% 3.62/1.05      | v7_waybel_0(X2) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_12813,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_12801,c_8695]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_4,plain,
% 3.62/1.05      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f66]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | l1_waybel_0(X0,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_struct_0(X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f78]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_541,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | l1_waybel_0(X0,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X3)
% 3.62/1.05      | X1 != X3 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_542,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | l1_waybel_0(X0,X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X1) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_541]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1814,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | l1_waybel_0(X0,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_542,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1815,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | l1_waybel_0(X0,sK6)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1814]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1817,plain,
% 3.62/1.05      ( v2_struct_0(X1)
% 3.62/1.05      | l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(global_propositional_subsumption,[status(thm)],[c_1815,c_39]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1818,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | l1_waybel_0(X0,sK6)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1817]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1819,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_14,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_struct_0(X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f77]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_513,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X3)
% 3.62/1.05      | X1 != X3 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_514,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_513]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1840,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | v7_waybel_0(X0)
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_514,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1841,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | v7_waybel_0(X0) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1840]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1843,plain,
% 3.62/1.05      ( v2_struct_0(X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | v7_waybel_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,[status(thm)],[c_1841,c_39]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1844,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1843]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1845,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1844]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_15,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_struct_0(X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f76]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_485,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X3)
% 3.62/1.05      | X1 != X3 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_486,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X1) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_485]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1866,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_486,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1867,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1866]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1869,plain,
% 3.62/1.05      ( v2_struct_0(X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(global_propositional_subsumption,[status(thm)],[c_1867,c_39]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1870,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1869]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1871,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v4_orders_2(X0) = iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1870]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_16,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | ~ v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_struct_0(X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f75]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_457,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | ~ v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X3)
% 3.62/1.05      | X1 != X3 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_458,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | ~ v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ l1_pre_topc(X1) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_457]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1892,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,X1,X2)
% 3.62/1.05      | ~ l1_waybel_0(X2,X1)
% 3.62/1.05      | ~ v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_458,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1893,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | ~ v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1892]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1895,plain,
% 3.62/1.05      ( v2_struct_0(X1)
% 3.62/1.05      | ~ v2_struct_0(X0)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(global_propositional_subsumption,[status(thm)],[c_1893,c_39]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1896,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | ~ v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1895]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1897,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1896]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13244,plain,
% 3.62/1.05      ( v4_orders_2(X1) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_12813,c_1819,c_1845,c_1871,c_1897]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13245,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_13244]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13256,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8686,c_13245]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13313,plain,
% 3.62/1.05      ( v4_orders_2(X1) != iProver_top
% 3.62/1.05      | m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_13256,c_1819,c_1845,c_1871,c_1897,c_9424]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13314,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,X1,sK0(sK6,X0,k1_xboole_0)) = iProver_top
% 3.62/1.05      | m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_13313]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_23,plain,
% 3.62/1.05      ( ~ r3_waybel_9(X0,sK4(X0),X1)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.62/1.05      | v1_compts_1(X0)
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f91]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1211,plain,
% 3.62/1.05      ( ~ r3_waybel_9(X0,sK4(X0),X1)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.62/1.05      | v1_compts_1(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1212,plain,
% 3.62/1.05      ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
% 3.62/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1211]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1216,plain,
% 3.62/1.05      ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
% 3.62/1.05      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.62/1.05      | v1_compts_1(sK6) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1212,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8698,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,sK4(sK6),X0) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13326,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
% 3.62/1.05      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.62/1.05      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_13314,c_8698]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_27,plain,
% 3.62/1.05      ( v1_compts_1(X0)
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v2_struct_0(sK4(X0))
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f87]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1155,plain,
% 3.62/1.05      ( v1_compts_1(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v2_struct_0(sK4(X0))
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1156,plain,
% 3.62/1.05      ( v1_compts_1(sK6)
% 3.62/1.05      | ~ v2_struct_0(sK4(sK6))
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1155]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1158,plain,
% 3.62/1.05      ( v1_compts_1(sK6) | ~ v2_struct_0(sK4(sK6)) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1156,c_39,c_38,c_37,c_63]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1160,plain,
% 3.62/1.05      ( v1_compts_1(sK6) = iProver_top | v2_struct_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1158]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_26,plain,
% 3.62/1.05      ( v1_compts_1(X0)
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v4_orders_2(sK4(X0))
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f88]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1169,plain,
% 3.62/1.05      ( v1_compts_1(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v4_orders_2(sK4(X0))
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1170,plain,
% 3.62/1.05      ( v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | v4_orders_2(sK4(sK6))
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1169]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1172,plain,
% 3.62/1.05      ( v4_orders_2(sK4(sK6)) | v1_compts_1(sK6) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1170,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1173,plain,
% 3.62/1.05      ( v1_compts_1(sK6) | v4_orders_2(sK4(sK6)) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1172]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1174,plain,
% 3.62/1.05      ( v1_compts_1(sK6) = iProver_top | v4_orders_2(sK4(sK6)) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_25,plain,
% 3.62/1.05      ( v1_compts_1(X0)
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v7_waybel_0(sK4(X0))
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f89]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1183,plain,
% 3.62/1.05      ( v1_compts_1(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v7_waybel_0(sK4(X0))
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_25,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1184,plain,
% 3.62/1.05      ( v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | v7_waybel_0(sK4(sK6))
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1183]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1186,plain,
% 3.62/1.05      ( v7_waybel_0(sK4(sK6)) | v1_compts_1(sK6) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1184,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1187,plain,
% 3.62/1.05      ( v1_compts_1(sK6) | v7_waybel_0(sK4(sK6)) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1186]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1188,plain,
% 3.62/1.05      ( v1_compts_1(sK6) = iProver_top | v7_waybel_0(sK4(sK6)) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1187]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_24,plain,
% 3.62/1.05      ( l1_waybel_0(sK4(X0),X0)
% 3.62/1.05      | v1_compts_1(X0)
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f90]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1197,plain,
% 3.62/1.05      ( l1_waybel_0(sK4(X0),X0)
% 3.62/1.05      | v1_compts_1(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_24,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1198,plain,
% 3.62/1.05      ( l1_waybel_0(sK4(sK6),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1197]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1200,plain,
% 3.62/1.05      ( l1_waybel_0(sK4(sK6),sK6) | v1_compts_1(sK6) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1198,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1202,plain,
% 3.62/1.05      ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13413,plain,
% 3.62/1.05      ( v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_13326,c_1160,c_1174,c_1188,c_1202]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13414,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
% 3.62/1.05      | m1_subset_1(sK0(sK6,X0,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_13413]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13423,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8686,c_13414]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9323,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK4(sK6))
% 3.62/1.05      | l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.62/1.05      | v2_struct_0(sK4(sK6))
% 3.62/1.05      | ~ v4_orders_2(sK4(sK6))
% 3.62/1.05      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_1818]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9324,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) = iProver_top
% 3.62/1.05      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.62/1.05      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9323]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9322,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK4(sK6))
% 3.62/1.05      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.62/1.05      | v2_struct_0(sK4(sK6))
% 3.62/1.05      | ~ v4_orders_2(sK4(sK6))
% 3.62/1.05      | v7_waybel_0(X0)
% 3.62/1.05      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_1844]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9328,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
% 3.62/1.05      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.62/1.05      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) = iProver_top
% 3.62/1.05      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9322]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9321,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK4(sK6))
% 3.62/1.05      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.62/1.05      | v2_struct_0(sK4(sK6))
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v4_orders_2(sK4(sK6))
% 3.62/1.05      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_1870]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9332,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
% 3.62/1.05      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9321]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13428,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK4(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_13423,c_1160,c_1174,c_1188,c_1202,c_9324,c_9328,c_9332,
% 3.62/1.05                 c_9424]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13438,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
% 3.62/1.05      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.62/1.05      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.62/1.05      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8707,c_13428]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2447,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | l1_waybel_0(X2,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | X1 != X0
% 3.62/1.05      | sK8(X0) != X2
% 3.62/1.05      | sK6 != sK6 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_36,c_1818]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2448,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | l1_waybel_0(sK8(X0),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_2447]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2423,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | v7_waybel_0(X2)
% 3.62/1.05      | X1 != X0
% 3.62/1.05      | sK8(X0) != X2
% 3.62/1.05      | sK6 != sK6 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_36,c_1844]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2424,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | v7_waybel_0(sK8(X0)) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_2423]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2399,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | v4_orders_2(X2)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | X1 != X0
% 3.62/1.05      | sK8(X0) != X2
% 3.62/1.05      | sK6 != sK6 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_36,c_1870]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2400,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | v4_orders_2(sK8(X0))
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_2399]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2375,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(X1,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | ~ v2_struct_0(X2)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | X1 != X0
% 3.62/1.05      | sK8(X0) != X2
% 3.62/1.05      | sK6 != sK6 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_36,c_1896]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2376,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v2_struct_0(sK8(X0))
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_2375]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_18,plain,
% 3.62/1.05      ( ~ v3_yellow_6(X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | ~ v2_pre_topc(X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 3.62/1.05      inference(cnf_transformation,[],[f79]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_35,negated_conjecture,
% 3.62/1.05      ( v3_yellow_6(sK8(X0),sK6)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f96]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_639,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X2,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | ~ v2_pre_topc(X1)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X2)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X2)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k10_yellow_6(X1,X0) != k1_xboole_0
% 3.62/1.05      | sK8(X2) != X0
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_640,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | ~ v2_pre_topc(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK8(X0))
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v4_orders_2(sK8(X0))
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v7_waybel_0(sK8(X0))
% 3.62/1.05      | ~ l1_pre_topc(sK6)
% 3.62/1.05      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_639]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_644,plain,
% 3.62/1.05      ( ~ v7_waybel_0(sK8(X0))
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(sK8(X0))
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK8(X0))
% 3.62/1.05      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_640,c_39,c_38,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_645,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK8(X0))
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v4_orders_2(sK8(X0))
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v7_waybel_0(sK8(X0))
% 3.62/1.05      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_644]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2630,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v4_orders_2(sK8(X0))
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v7_waybel_0(sK8(X0))
% 3.62/1.05      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.62/1.05      inference(backward_subsumption_resolution,[status(thm)],[c_2376,c_645]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2641,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v7_waybel_0(sK8(X0))
% 3.62/1.05      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.62/1.05      inference(backward_subsumption_resolution,[status(thm)],[c_2400,c_2630]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2652,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.62/1.05      inference(backward_subsumption_resolution,[status(thm)],[c_2424,c_2641]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_2658,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.62/1.05      inference(backward_subsumption_resolution,[status(thm)],[c_2448,c_2652]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9460,plain,
% 3.62/1.05      ( ~ l1_waybel_0(sK4(sK6),sK6)
% 3.62/1.05      | v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(sK4(sK6))
% 3.62/1.05      | ~ v4_orders_2(sK4(sK6))
% 3.62/1.05      | ~ v7_waybel_0(sK4(sK6))
% 3.62/1.05      | k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0 ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_2658]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9461,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0
% 3.62/1.05      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.62/1.05      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9460]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8699,plain,
% 3.62/1.05      ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1200]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8681,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X1,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) != iProver_top
% 3.62/1.05      | v2_struct_0(X1) = iProver_top
% 3.62/1.05      | v4_orders_2(X1) != iProver_top
% 3.62/1.05      | v7_waybel_0(X1) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1896]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9318,plain,
% 3.62/1.05      ( l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(sK8(X0)) != iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8707,c_8681]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9628,plain,
% 3.62/1.05      ( v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(sK8(sK4(sK6))) != iProver_top
% 3.62/1.05      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.62/1.05      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8699,c_9318]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10427,plain,
% 3.62/1.05      ( v2_struct_0(sK8(sK4(sK6))) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) = iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_9628,c_1160,c_1174,c_1188]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10428,plain,
% 3.62/1.05      ( v1_compts_1(sK6) = iProver_top
% 3.62/1.05      | v2_struct_0(sK8(sK4(sK6))) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_10427]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_13481,plain,
% 3.62/1.05      ( v1_compts_1(sK6) = iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_13438,c_1160,c_1174,c_1188,c_1202,c_9461,c_10428]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_28,plain,
% 3.62/1.05      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | ~ v1_compts_1(X0)
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f86]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1125,plain,
% 3.62/1.05      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | ~ v1_compts_1(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_28,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1126,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1125]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1130,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1126,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1131,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1130]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8703,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,sK5(sK6,X0)) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_22,plain,
% 3.62/1.05      ( ~ r3_waybel_9(X0,X1,X2)
% 3.62/1.05      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | ~ v2_pre_topc(X0)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0) ),
% 3.62/1.05      inference(cnf_transformation,[],[f83]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1232,plain,
% 3.62/1.05      ( ~ r3_waybel_9(X0,X1,X2)
% 3.62/1.05      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X1,X0)
% 3.62/1.05      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X0)
% 3.62/1.05      | sK6 != X0 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_22,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1233,plain,
% 3.62/1.05      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1232]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1237,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1233,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1238,plain,
% 3.62/1.05      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.05      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1237]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8697,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1) != iProver_top
% 3.62/1.05      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0) = iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_17,plain,
% 3.62/1.05      ( v3_yellow_6(X0,X1)
% 3.62/1.05      | ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | ~ v2_pre_topc(X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 3.62/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_30,negated_conjecture,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | ~ v3_yellow_6(X0,sK6)
% 3.62/1.05      | ~ v1_compts_1(sK6) ),
% 3.62/1.05      inference(cnf_transformation,[],[f101]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_606,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | ~ l1_waybel_0(X1,X2)
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | ~ v2_pre_topc(X2)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X2)
% 3.62/1.05      | ~ v4_orders_2(X1)
% 3.62/1.05      | ~ v7_waybel_0(X1)
% 3.62/1.05      | ~ l1_pre_topc(X2)
% 3.62/1.05      | X0 != X1
% 3.62/1.05      | k10_yellow_6(X2,X1) = k1_xboole_0
% 3.62/1.05      | sK6 != X2 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_607,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | ~ v2_pre_topc(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_606]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_611,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_607,c_39,c_38,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_612,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_611]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_8704,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK7) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_34,negated_conjecture,
% 3.62/1.05      ( ~ v1_compts_1(sK6) | ~ v2_struct_0(sK7) ),
% 3.62/1.05      inference(cnf_transformation,[],[f97]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_49,plain,
% 3.62/1.05      ( v1_compts_1(sK6) != iProver_top | v2_struct_0(sK7) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_33,negated_conjecture,
% 3.62/1.05      ( ~ v1_compts_1(sK6) | v4_orders_2(sK7) ),
% 3.62/1.05      inference(cnf_transformation,[],[f98]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_50,plain,
% 3.62/1.05      ( v1_compts_1(sK6) != iProver_top | v4_orders_2(sK7) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_32,negated_conjecture,
% 3.62/1.05      ( ~ v1_compts_1(sK6) | v7_waybel_0(sK7) ),
% 3.62/1.05      inference(cnf_transformation,[],[f99]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_51,plain,
% 3.62/1.05      ( v1_compts_1(sK6) != iProver_top | v7_waybel_0(sK7) = iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_31,negated_conjecture,
% 3.62/1.05      ( l1_waybel_0(sK7,sK6) | ~ v1_compts_1(sK6) ),
% 3.62/1.05      inference(cnf_transformation,[],[f100]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_52,plain,
% 3.62/1.05      ( l1_waybel_0(sK7,sK6) = iProver_top | v1_compts_1(sK6) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_613,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK7) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9148,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | l1_waybel_0(X0,sK6)
% 3.62/1.05      | ~ l1_waybel_0(sK7,sK6)
% 3.62/1.05      | v2_struct_0(sK7)
% 3.62/1.05      | ~ v4_orders_2(sK7)
% 3.62/1.05      | ~ v7_waybel_0(sK7) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_1818]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9149,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,sK7) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) = iProver_top
% 3.62/1.05      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK7) = iProver_top
% 3.62/1.05      | v4_orders_2(sK7) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9148]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9153,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | ~ l1_waybel_0(sK7,sK6)
% 3.62/1.05      | v2_struct_0(sK7)
% 3.62/1.05      | ~ v4_orders_2(sK7)
% 3.62/1.05      | v7_waybel_0(X0)
% 3.62/1.05      | ~ v7_waybel_0(sK7) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_1844]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9154,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,sK7) != iProver_top
% 3.62/1.05      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK7) = iProver_top
% 3.62/1.05      | v4_orders_2(sK7) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) = iProver_top
% 3.62/1.05      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9153]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9158,plain,
% 3.62/1.05      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.62/1.05      | ~ l1_waybel_0(sK7,sK6)
% 3.62/1.05      | v2_struct_0(sK7)
% 3.62/1.05      | v4_orders_2(X0)
% 3.62/1.05      | ~ v4_orders_2(sK7)
% 3.62/1.05      | ~ v7_waybel_0(sK7) ),
% 3.62/1.05      inference(instantiation,[status(thm)],[c_1870]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9159,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,sK7) != iProver_top
% 3.62/1.05      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK7) = iProver_top
% 3.62/1.05      | v4_orders_2(X0) = iProver_top
% 3.62/1.05      | v4_orders_2(sK7) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.05      inference(predicate_to_equality,[status(thm)],[c_9158]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10331,plain,
% 3.62/1.05      ( m2_yellow_6(X0,sK6,sK7) != iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_8704,c_49,c_50,c_51,c_52,c_613,c_9149,c_9154,c_9159]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10332,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,X0) = k1_xboole_0
% 3.62/1.05      | m2_yellow_6(X0,sK6,sK7) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_10331]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10581,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,sK7,X0) != iProver_top
% 3.62/1.05      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK3(sK6,sK7,X0)) = iProver_top
% 3.62/1.05      | v2_struct_0(sK7) = iProver_top
% 3.62/1.05      | v4_orders_2(sK7) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8697,c_10332]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10585,plain,
% 3.62/1.05      ( r3_waybel_9(sK6,X0,X1) != iProver_top
% 3.62/1.05      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v2_struct_0(X0) = iProver_top
% 3.62/1.05      | v2_struct_0(sK3(sK6,X0,X1)) != iProver_top
% 3.62/1.05      | v4_orders_2(X0) != iProver_top
% 3.62/1.05      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8697,c_8681]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_10651,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,sK7,X0) != iProver_top
% 3.62/1.05      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK7) = iProver_top
% 3.62/1.05      | v4_orders_2(sK7) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_10581,c_10585]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11569,plain,
% 3.62/1.05      ( v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,sK7,X0) != iProver_top ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_10651,c_49,c_50,c_51,c_52]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11570,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0)) = k1_xboole_0
% 3.62/1.05      | r3_waybel_9(sK6,sK7,X0) != iProver_top
% 3.62/1.05      | m1_subset_1(X0,u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_11569]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_11579,plain,
% 3.62/1.05      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
% 3.62/1.05      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.05      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
% 3.62/1.05      | v1_compts_1(sK6) != iProver_top
% 3.62/1.05      | v2_struct_0(sK7) = iProver_top
% 3.62/1.05      | v4_orders_2(sK7) != iProver_top
% 3.62/1.05      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.05      inference(superposition,[status(thm)],[c_8703,c_11570]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_29,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.62/1.05      | ~ v1_compts_1(X1)
% 3.62/1.05      | ~ v2_pre_topc(X1)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1) ),
% 3.62/1.05      inference(cnf_transformation,[],[f85]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1507,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,X1)
% 3.62/1.05      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.62/1.05      | ~ v1_compts_1(X1)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(X1)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(X1)
% 3.62/1.05      | sK6 != X1 ),
% 3.62/1.05      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1508,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | v2_struct_0(sK6)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ l1_pre_topc(sK6) ),
% 3.62/1.05      inference(unflattening,[status(thm)],[c_1507]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1512,plain,
% 3.62/1.05      ( ~ v7_waybel_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0) ),
% 3.62/1.05      inference(global_propositional_subsumption,
% 3.62/1.05                [status(thm)],
% 3.62/1.05                [c_1508,c_39,c_37]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_1513,plain,
% 3.62/1.05      ( ~ l1_waybel_0(X0,sK6)
% 3.62/1.05      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(X0)
% 3.62/1.05      | ~ v4_orders_2(X0)
% 3.62/1.05      | ~ v7_waybel_0(X0) ),
% 3.62/1.05      inference(renaming,[status(thm)],[c_1512]) ).
% 3.62/1.05  
% 3.62/1.05  cnf(c_9136,plain,
% 3.62/1.05      ( ~ l1_waybel_0(sK7,sK6)
% 3.62/1.05      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6))
% 3.62/1.05      | ~ v1_compts_1(sK6)
% 3.62/1.05      | v2_struct_0(sK7)
% 3.62/1.05      | ~ v4_orders_2(sK7)
% 3.62/1.05      | ~ v7_waybel_0(sK7) ),
% 3.62/1.06      inference(instantiation,[status(thm)],[c_1513]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_9137,plain,
% 3.62/1.06      ( l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.06      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) = iProver_top
% 3.62/1.06      | v1_compts_1(sK6) != iProver_top
% 3.62/1.06      | v2_struct_0(sK7) = iProver_top
% 3.62/1.06      | v4_orders_2(sK7) != iProver_top
% 3.62/1.06      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.06      inference(predicate_to_equality,[status(thm)],[c_9136]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_11697,plain,
% 3.62/1.06      ( v1_compts_1(sK6) != iProver_top
% 3.62/1.06      | k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
% 3.62/1.06      inference(global_propositional_subsumption,
% 3.62/1.06                [status(thm)],
% 3.62/1.06                [c_11579,c_49,c_50,c_51,c_52,c_9137]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_11698,plain,
% 3.62/1.06      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
% 3.62/1.06      | v1_compts_1(sK6) != iProver_top ),
% 3.62/1.06      inference(renaming,[status(thm)],[c_11697]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_13486,plain,
% 3.62/1.06      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
% 3.62/1.06      inference(superposition,[status(thm)],[c_13481,c_11698]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_21,plain,
% 3.62/1.06      ( ~ r3_waybel_9(X0,X1,X2)
% 3.62/1.06      | ~ l1_waybel_0(X1,X0)
% 3.62/1.06      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 3.62/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.06      | ~ v2_pre_topc(X0)
% 3.62/1.06      | v2_struct_0(X0)
% 3.62/1.06      | v2_struct_0(X1)
% 3.62/1.06      | ~ v4_orders_2(X1)
% 3.62/1.06      | ~ v7_waybel_0(X1)
% 3.62/1.06      | ~ l1_pre_topc(X0) ),
% 3.62/1.06      inference(cnf_transformation,[],[f84]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_1265,plain,
% 3.62/1.06      ( ~ r3_waybel_9(X0,X1,X2)
% 3.62/1.06      | ~ l1_waybel_0(X1,X0)
% 3.62/1.06      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 3.62/1.06      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.62/1.06      | v2_struct_0(X0)
% 3.62/1.06      | v2_struct_0(X1)
% 3.62/1.06      | ~ v4_orders_2(X1)
% 3.62/1.06      | ~ v7_waybel_0(X1)
% 3.62/1.06      | ~ l1_pre_topc(X0)
% 3.62/1.06      | sK6 != X0 ),
% 3.62/1.06      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_1266,plain,
% 3.62/1.06      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.06      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.06      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.62/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.06      | v2_struct_0(X0)
% 3.62/1.06      | v2_struct_0(sK6)
% 3.62/1.06      | ~ v4_orders_2(X0)
% 3.62/1.06      | ~ v7_waybel_0(X0)
% 3.62/1.06      | ~ l1_pre_topc(sK6) ),
% 3.62/1.06      inference(unflattening,[status(thm)],[c_1265]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_1270,plain,
% 3.62/1.06      ( ~ v7_waybel_0(X0)
% 3.62/1.06      | ~ v4_orders_2(X0)
% 3.62/1.06      | ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.06      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.06      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.62/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.06      | v2_struct_0(X0) ),
% 3.62/1.06      inference(global_propositional_subsumption,
% 3.62/1.06                [status(thm)],
% 3.62/1.06                [c_1266,c_39,c_37]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_1271,plain,
% 3.62/1.06      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.62/1.06      | ~ l1_waybel_0(X0,sK6)
% 3.62/1.06      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.62/1.06      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.62/1.06      | v2_struct_0(X0)
% 3.62/1.06      | ~ v4_orders_2(X0)
% 3.62/1.06      | ~ v7_waybel_0(X0) ),
% 3.62/1.06      inference(renaming,[status(thm)],[c_1270]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_8696,plain,
% 3.62/1.06      ( r3_waybel_9(sK6,X0,X1) != iProver_top
% 3.62/1.06      | l1_waybel_0(X0,sK6) != iProver_top
% 3.62/1.06      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1))) = iProver_top
% 3.62/1.06      | m1_subset_1(X1,u1_struct_0(sK6)) != iProver_top
% 3.62/1.06      | v2_struct_0(X0) = iProver_top
% 3.62/1.06      | v4_orders_2(X0) != iProver_top
% 3.62/1.06      | v7_waybel_0(X0) != iProver_top ),
% 3.62/1.06      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_13704,plain,
% 3.62/1.06      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) != iProver_top
% 3.62/1.06      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.06      | r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top
% 3.62/1.06      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
% 3.62/1.06      | v2_struct_0(sK7) = iProver_top
% 3.62/1.06      | v4_orders_2(sK7) != iProver_top
% 3.62/1.06      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.06      inference(superposition,[status(thm)],[c_13486,c_8696]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_9145,plain,
% 3.62/1.06      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7))
% 3.62/1.06      | ~ l1_waybel_0(sK7,sK6)
% 3.62/1.06      | ~ v1_compts_1(sK6)
% 3.62/1.06      | v2_struct_0(sK7)
% 3.62/1.06      | ~ v4_orders_2(sK7)
% 3.62/1.06      | ~ v7_waybel_0(sK7) ),
% 3.62/1.06      inference(instantiation,[status(thm)],[c_1131]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_9146,plain,
% 3.62/1.06      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) = iProver_top
% 3.62/1.06      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.62/1.06      | v1_compts_1(sK6) != iProver_top
% 3.62/1.06      | v2_struct_0(sK7) = iProver_top
% 3.62/1.06      | v4_orders_2(sK7) != iProver_top
% 3.62/1.06      | v7_waybel_0(sK7) != iProver_top ),
% 3.62/1.06      inference(predicate_to_equality,[status(thm)],[c_9145]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_13757,plain,
% 3.62/1.06      ( r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top ),
% 3.62/1.06      inference(global_propositional_subsumption,
% 3.62/1.06                [status(thm)],
% 3.62/1.06                [c_13704,c_49,c_50,c_51,c_52,c_1160,c_1174,c_1188,c_1202,
% 3.62/1.06                 c_9137,c_9146,c_9461,c_10428,c_13438]) ).
% 3.62/1.06  
% 3.62/1.06  cnf(c_13762,plain,
% 3.62/1.06      ( $false ),
% 3.62/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_13757,c_9307]) ).
% 3.62/1.06  
% 3.62/1.06  
% 3.62/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/1.06  
% 3.62/1.06  ------                               Statistics
% 3.62/1.06  
% 3.62/1.06  ------ General
% 3.62/1.06  
% 3.62/1.06  abstr_ref_over_cycles:                  0
% 3.62/1.06  abstr_ref_under_cycles:                 0
% 3.62/1.06  gc_basic_clause_elim:                   0
% 3.62/1.06  forced_gc_time:                         0
% 3.62/1.06  parsing_time:                           0.022
% 3.62/1.06  unif_index_cands_time:                  0.
% 3.62/1.06  unif_index_add_time:                    0.
% 3.62/1.06  orderings_time:                         0.
% 3.62/1.06  out_proof_time:                         0.024
% 3.62/1.06  total_time:                             0.412
% 3.62/1.06  num_of_symbols:                         60
% 3.62/1.06  num_of_terms:                           6240
% 3.62/1.06  
% 3.62/1.06  ------ Preprocessing
% 3.62/1.06  
% 3.62/1.06  num_of_splits:                          0
% 3.62/1.06  num_of_split_atoms:                     0
% 3.62/1.06  num_of_reused_defs:                     0
% 3.62/1.06  num_eq_ax_congr_red:                    47
% 3.62/1.06  num_of_sem_filtered_clauses:            1
% 3.62/1.06  num_of_subtypes:                        0
% 3.62/1.06  monotx_restored_types:                  0
% 3.62/1.06  sat_num_of_epr_types:                   0
% 3.62/1.06  sat_num_of_non_cyclic_types:            0
% 3.62/1.06  sat_guarded_non_collapsed_types:        0
% 3.62/1.06  num_pure_diseq_elim:                    0
% 3.62/1.06  simp_replaced_by:                       0
% 3.62/1.06  res_preprocessed:                       187
% 3.62/1.06  prep_upred:                             0
% 3.62/1.06  prep_unflattend:                        207
% 3.62/1.06  smt_new_axioms:                         0
% 3.62/1.06  pred_elim_cands:                        11
% 3.62/1.06  pred_elim:                              5
% 3.62/1.06  pred_elim_cl:                           6
% 3.62/1.06  pred_elim_cycles:                       17
% 3.62/1.06  merged_defs:                            0
% 3.62/1.06  merged_defs_ncl:                        0
% 3.62/1.06  bin_hyper_res:                          0
% 3.62/1.06  prep_cycles:                            4
% 3.62/1.06  pred_elim_time:                         0.163
% 3.62/1.06  splitting_time:                         0.
% 3.62/1.06  sem_filter_time:                        0.
% 3.62/1.06  monotx_time:                            0.001
% 3.62/1.06  subtype_inf_time:                       0.
% 3.62/1.06  
% 3.62/1.06  ------ Problem properties
% 3.62/1.06  
% 3.62/1.06  clauses:                                34
% 3.62/1.06  conjectures:                            6
% 3.62/1.06  epr:                                    9
% 3.62/1.06  horn:                                   11
% 3.62/1.06  ground:                                 9
% 3.62/1.06  unary:                                  2
% 3.62/1.06  binary:                                 9
% 3.62/1.06  lits:                                   169
% 3.62/1.06  lits_eq:                                6
% 3.62/1.06  fd_pure:                                0
% 3.62/1.06  fd_pseudo:                              0
% 3.62/1.06  fd_cond:                                0
% 3.62/1.06  fd_pseudo_cond:                         4
% 3.62/1.06  ac_symbols:                             0
% 3.62/1.06  
% 3.62/1.06  ------ Propositional Solver
% 3.62/1.06  
% 3.62/1.06  prop_solver_calls:                      28
% 3.62/1.06  prop_fast_solver_calls:                 4790
% 3.62/1.06  smt_solver_calls:                       0
% 3.62/1.06  smt_fast_solver_calls:                  0
% 3.62/1.06  prop_num_of_clauses:                    2622
% 3.62/1.06  prop_preprocess_simplified:             9675
% 3.62/1.06  prop_fo_subsumed:                       170
% 3.62/1.06  prop_solver_time:                       0.
% 3.62/1.06  smt_solver_time:                        0.
% 3.62/1.06  smt_fast_solver_time:                   0.
% 3.62/1.06  prop_fast_solver_time:                  0.
% 3.62/1.06  prop_unsat_core_time:                   0.
% 3.62/1.06  
% 3.62/1.06  ------ QBF
% 3.62/1.06  
% 3.62/1.06  qbf_q_res:                              0
% 3.62/1.06  qbf_num_tautologies:                    0
% 3.62/1.06  qbf_prep_cycles:                        0
% 3.62/1.06  
% 3.62/1.06  ------ BMC1
% 3.62/1.06  
% 3.62/1.06  bmc1_current_bound:                     -1
% 3.62/1.06  bmc1_last_solved_bound:                 -1
% 3.62/1.06  bmc1_unsat_core_size:                   -1
% 3.62/1.06  bmc1_unsat_core_parents_size:           -1
% 3.62/1.06  bmc1_merge_next_fun:                    0
% 3.62/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.62/1.06  
% 3.62/1.06  ------ Instantiation
% 3.62/1.06  
% 3.62/1.06  inst_num_of_clauses:                    654
% 3.62/1.06  inst_num_in_passive:                    62
% 3.62/1.06  inst_num_in_active:                     411
% 3.62/1.06  inst_num_in_unprocessed:                181
% 3.62/1.06  inst_num_of_loops:                      460
% 3.62/1.06  inst_num_of_learning_restarts:          0
% 3.62/1.06  inst_num_moves_active_passive:          46
% 3.62/1.06  inst_lit_activity:                      0
% 3.62/1.06  inst_lit_activity_moves:                0
% 3.62/1.06  inst_num_tautologies:                   0
% 3.62/1.06  inst_num_prop_implied:                  0
% 3.62/1.06  inst_num_existing_simplified:           0
% 3.62/1.06  inst_num_eq_res_simplified:             0
% 3.62/1.06  inst_num_child_elim:                    0
% 3.62/1.06  inst_num_of_dismatching_blockings:      42
% 3.62/1.06  inst_num_of_non_proper_insts:           418
% 3.62/1.06  inst_num_of_duplicates:                 0
% 3.62/1.06  inst_inst_num_from_inst_to_res:         0
% 3.62/1.06  inst_dismatching_checking_time:         0.
% 3.62/1.06  
% 3.62/1.06  ------ Resolution
% 3.62/1.06  
% 3.62/1.06  res_num_of_clauses:                     0
% 3.62/1.06  res_num_in_passive:                     0
% 3.62/1.06  res_num_in_active:                      0
% 3.62/1.06  res_num_of_loops:                       191
% 3.62/1.06  res_forward_subset_subsumed:            22
% 3.62/1.06  res_backward_subset_subsumed:           0
% 3.62/1.06  res_forward_subsumed:                   0
% 3.62/1.06  res_backward_subsumed:                  0
% 3.62/1.06  res_forward_subsumption_resolution:     21
% 3.62/1.06  res_backward_subsumption_resolution:    6
% 3.62/1.06  res_clause_to_clause_subsumption:       1354
% 3.62/1.06  res_orphan_elimination:                 0
% 3.62/1.06  res_tautology_del:                      39
% 3.62/1.06  res_num_eq_res_simplified:              0
% 3.62/1.06  res_num_sel_changes:                    0
% 3.62/1.06  res_moves_from_active_to_pass:          0
% 3.62/1.06  
% 3.62/1.06  ------ Superposition
% 3.62/1.06  
% 3.62/1.06  sup_time_total:                         0.
% 3.62/1.06  sup_time_generating:                    0.
% 3.62/1.06  sup_time_sim_full:                      0.
% 3.62/1.06  sup_time_sim_immed:                     0.
% 3.62/1.06  
% 3.62/1.06  sup_num_of_clauses:                     97
% 3.62/1.06  sup_num_in_active:                      83
% 3.62/1.06  sup_num_in_passive:                     14
% 3.62/1.06  sup_num_of_loops:                       91
% 3.62/1.06  sup_fw_superposition:                   36
% 3.62/1.06  sup_bw_superposition:                   58
% 3.62/1.06  sup_immediate_simplified:               13
% 3.62/1.06  sup_given_eliminated:                   0
% 3.62/1.06  comparisons_done:                       0
% 3.62/1.06  comparisons_avoided:                    0
% 3.62/1.06  
% 3.62/1.06  ------ Simplifications
% 3.62/1.06  
% 3.62/1.06  
% 3.62/1.06  sim_fw_subset_subsumed:                 3
% 3.62/1.06  sim_bw_subset_subsumed:                 9
% 3.62/1.06  sim_fw_subsumed:                        9
% 3.62/1.06  sim_bw_subsumed:                        0
% 3.62/1.06  sim_fw_subsumption_res:                 27
% 3.62/1.06  sim_bw_subsumption_res:                 0
% 3.62/1.06  sim_tautology_del:                      12
% 3.62/1.06  sim_eq_tautology_del:                   0
% 3.62/1.06  sim_eq_res_simp:                        0
% 3.62/1.06  sim_fw_demodulated:                     0
% 3.62/1.06  sim_bw_demodulated:                     0
% 3.62/1.06  sim_light_normalised:                   1
% 3.62/1.06  sim_joinable_taut:                      0
% 3.62/1.06  sim_joinable_simp:                      0
% 3.62/1.06  sim_ac_normalised:                      0
% 3.62/1.06  sim_smt_subsumption:                    0
% 3.62/1.06  
%------------------------------------------------------------------------------
