%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:27 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_63)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f56,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK8(X3),X0)
        & m2_yellow_6(sK8(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f53,f56,f55,f54])).

fof(f91,plain,(
    ! [X3] :
      ( m2_yellow_6(sK8(X3),sK6,X3)
      | ~ l1_waybel_0(X3,sK6)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f41,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
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

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
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
    inference(equality_resolution,[],[f65])).

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
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f26])).

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
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f49,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK5(X0,X3))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).

fof(f87,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK4(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK4(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ! [X3] :
      ( v3_yellow_6(sK8(X3),sK6)
      | ~ l1_waybel_0(X3,sK6)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f50])).

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
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
        & m2_yellow_6(sK3(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f44])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK6)
      | ~ m2_yellow_6(X2,sK6,sK7)
      | ~ v1_compts_1(sK6) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,
    ( ~ v2_struct_0(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,
    ( v4_orders_2(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,
    ( v7_waybel_0(sK7)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,
    ( l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f45])).

cnf(c_36,negated_conjecture,
    ( m2_yellow_6(sK8(X0),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_8117,negated_conjecture,
    ( m2_yellow_6(sK8(X0_57),sK6,X0_57)
    | ~ l1_waybel_0(X0_57,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_8828,plain,
    ( m2_yellow_6(sK8(X0_57),sK6,X0_57) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8117])).

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
    inference(cnf_transformation,[],[f66])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1741,plain,
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

cnf(c_1742,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_1741])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1746,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_39,c_37])).

cnf(c_1747,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = X1 ),
    inference(renaming,[status(thm)],[c_1746])).

cnf(c_8094,plain,
    ( ~ l1_waybel_0(X0_57,sK6)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
    | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,X0_57) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1747])).

cnf(c_8851,plain,
    ( k10_yellow_6(sK6,X0_57) = X0_58
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6)) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8094])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1666,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_38])).

cnf(c_1667,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1666])).

cnf(c_1671,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1667,c_39,c_37])).

cnf(c_1672,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1671])).

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
    inference(cnf_transformation,[],[f99])).

cnf(c_1492,plain,
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

cnf(c_1493,plain,
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
    inference(unflattening,[status(thm)],[c_1492])).

cnf(c_1497,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_39,c_37])).

cnf(c_1498,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1497])).

cnf(c_1689,plain,
    ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1672,c_1498])).

cnf(c_8097,plain,
    ( m1_connsp_2(sK2(sK6,X0_57,X0_58),sK6,X0_58)
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1689])).

cnf(c_8848,plain,
    ( m1_connsp_2(sK2(sK6,X0_57,X0_58),sK6,X0_58) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57)) = iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8097])).

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
    inference(cnf_transformation,[],[f67])).

cnf(c_1774,plain,
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

cnf(c_1775,plain,
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
    inference(unflattening,[status(thm)],[c_1774])).

cnf(c_1779,plain,
    ( ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1775,c_39,c_37])).

cnf(c_1780,plain,
    ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
    | r1_waybel_0(sK6,X1,X0)
    | ~ l1_waybel_0(X1,sK6)
    | r2_hidden(sK0(sK6,X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | k10_yellow_6(sK6,X1) = X2 ),
    inference(renaming,[status(thm)],[c_1779])).

cnf(c_8093,plain,
    ( ~ m1_connsp_2(X0_59,sK6,sK0(sK6,X0_57,X0_58))
    | r1_waybel_0(sK6,X0_57,X0_59)
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58)
    | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,X0_57) = X0_58 ),
    inference(subtyping,[status(esa)],[c_1780])).

cnf(c_8852,plain,
    ( k10_yellow_6(sK6,X0_57) = X0_58
    | m1_connsp_2(X0_59,sK6,sK0(sK6,X0_57,X0_58)) != iProver_top
    | r1_waybel_0(sK6,X0_57,X0_59) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8093])).

cnf(c_10522,plain,
    ( k10_yellow_6(sK6,X0_57) = X0_58
    | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,X0_58))) = iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
    | r2_hidden(sK0(sK6,X0_57,X0_58),k10_yellow_6(sK6,X1_57)) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8848,c_8852])).

cnf(c_8222,plain,
    ( k10_yellow_6(sK6,X0_57) = X0_58
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6)) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8094])).

cnf(c_10860,plain,
    ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | r2_hidden(sK0(sK6,X0_57,X0_58),k10_yellow_6(sK6,X1_57)) = iProver_top
    | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,X0_58))) = iProver_top
    | k10_yellow_6(sK6,X0_57) = X0_58
    | v2_struct_0(X1_57) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10522,c_8222])).

cnf(c_10861,plain,
    ( k10_yellow_6(sK6,X0_57) = X0_58
    | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,X0_58))) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
    | r2_hidden(sK0(sK6,X0_57,X0_58),k10_yellow_6(sK6,X1_57)) = iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_10860])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_555,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_556,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_8114,plain,
    ( ~ r2_hidden(X0_58,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_556])).

cnf(c_8831,plain,
    ( r2_hidden(X0_58,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8114])).

cnf(c_10868,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X1_57)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_10861,c_8831])).

cnf(c_1,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_306,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_307,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_546,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_307])).

cnf(c_547,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_8115,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_58)) ),
    inference(subtyping,[status(esa)],[c_547])).

cnf(c_9615,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(instantiation,[status(thm)],[c_8115])).

cnf(c_9616,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9615])).

cnf(c_10883,plain,
    ( r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X1_57)) = iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0))) = iProver_top
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10868,c_9616])).

cnf(c_10884,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X1_57)) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_10883])).

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
    inference(cnf_transformation,[],[f98])).

cnf(c_1528,plain,
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

cnf(c_1529,plain,
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
    inference(unflattening,[status(thm)],[c_1528])).

cnf(c_1533,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1529,c_39,c_37])).

cnf(c_1534,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1533])).

cnf(c_1690,plain,
    ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1672,c_1534])).

cnf(c_8096,plain,
    ( ~ r1_waybel_0(sK6,X0_57,sK2(sK6,X0_57,X0_58))
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1690])).

cnf(c_8849,plain,
    ( r1_waybel_0(sK6,X0_57,sK2(sK6,X0_57,X0_58)) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57)) = iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8096])).

cnf(c_10889,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X0_57)) = iProver_top
    | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_10884,c_8849])).

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
    inference(cnf_transformation,[],[f77])).

cnf(c_1459,plain,
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

cnf(c_1460,plain,
    ( r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1459])).

cnf(c_1464,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1460,c_39,c_37])).

cnf(c_1465,plain,
    ( r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1464])).

cnf(c_8102,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58)
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1465])).

cnf(c_8843,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57)) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8102])).

cnf(c_11136,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_10889,c_8843])).

cnf(c_11271,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8851,c_11136])).

cnf(c_11276,plain,
    ( l1_waybel_0(X0_57,sK6) != iProver_top
    | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11271,c_9616])).

cnf(c_11277,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_11276])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_1427,plain,
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

cnf(c_1428,plain,
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
    inference(unflattening,[status(thm)],[c_1427])).

cnf(c_1430,plain,
    ( ~ v7_waybel_0(X2)
    | ~ v4_orders_2(X2)
    | ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1428,c_39,c_37])).

cnf(c_1431,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | r3_waybel_9(sK6,X2,X1)
    | ~ m2_yellow_6(X0,sK6,X2)
    | ~ l1_waybel_0(X2,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(renaming,[status(thm)],[c_1430])).

cnf(c_8103,plain,
    ( ~ r3_waybel_9(sK6,X0_57,X0_58)
    | r3_waybel_9(sK6,X1_57,X0_58)
    | ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1431])).

cnf(c_8842,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | r3_waybel_9(sK6,X1_57,X0_58) = iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8103])).

cnf(c_10156,plain,
    ( k10_yellow_6(sK6,X0_57) = X0_58
    | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,X0_58)) != iProver_top
    | r3_waybel_9(sK6,X2_57,sK0(sK6,X0_57,X0_58)) = iProver_top
    | m2_yellow_6(X1_57,sK6,X2_57) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X2_57,sK6) != iProver_top
    | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X2_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X2_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X2_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8851,c_8842])).

cnf(c_11283,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_11277,c_10156])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_667,plain,
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

cnf(c_668,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_1943,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_668,c_37])).

cnf(c_1944,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X0,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1943])).

cnf(c_1946,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1944,c_39])).

cnf(c_1947,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | l1_waybel_0(X0,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1946])).

cnf(c_8092,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | l1_waybel_0(X0_57,sK6)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1947])).

cnf(c_8228,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | l1_waybel_0(X0_57,sK6) = iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8092])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_639,plain,
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

cnf(c_640,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_1969,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_640,c_37])).

cnf(c_1970,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1969])).

cnf(c_1972,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1970,c_39])).

cnf(c_1973,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1972])).

cnf(c_8091,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57)
    | v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1973])).

cnf(c_8229,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top
    | v7_waybel_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8091])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_611,plain,
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

cnf(c_612,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_1995,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_612,c_37])).

cnf(c_1996,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1995])).

cnf(c_1998,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1996,c_39])).

cnf(c_1999,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1998])).

cnf(c_8090,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | v4_orders_2(X0_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_1999])).

cnf(c_8230,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v4_orders_2(X0_57) = iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8090])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_583,plain,
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

cnf(c_584,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_2021,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_584,c_37])).

cnf(c_2022,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_2021])).

cnf(c_2024,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK6)
    | ~ m2_yellow_6(X0,sK6,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2022,c_39])).

cnf(c_2025,plain,
    ( ~ m2_yellow_6(X0,sK6,X1)
    | ~ l1_waybel_0(X1,sK6)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_2024])).

cnf(c_8089,plain,
    ( ~ m2_yellow_6(X0_57,sK6,X1_57)
    | ~ l1_waybel_0(X1_57,sK6)
    | ~ v2_struct_0(X0_57)
    | v2_struct_0(X1_57)
    | ~ v4_orders_2(X1_57)
    | ~ v7_waybel_0(X1_57) ),
    inference(subtyping,[status(esa)],[c_2025])).

cnf(c_8231,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8089])).

cnf(c_13065,plain,
    ( v4_orders_2(X1_57) != iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11283,c_8228,c_8229,c_8230,c_8231,c_9616])).

cnf(c_13066,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_13065])).

cnf(c_23,plain,
    ( ~ r3_waybel_9(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1340,plain,
    ( ~ r3_waybel_9(X0,sK4(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_38])).

cnf(c_1341,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1340])).

cnf(c_1345,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1341,c_39,c_37])).

cnf(c_8106,plain,
    ( ~ r3_waybel_9(sK6,sK4(sK6),X0_58)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v1_compts_1(sK6) ),
    inference(subtyping,[status(esa)],[c_1345])).

cnf(c_8839,plain,
    ( r3_waybel_9(sK6,sK4(sK6),X0_58) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8106])).

cnf(c_13071,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13066,c_8839])).

cnf(c_27,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1284,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_1285,plain,
    ( v1_compts_1(sK6)
    | ~ v2_struct_0(sK4(sK6))
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1284])).

cnf(c_1287,plain,
    ( v1_compts_1(sK6)
    | ~ v2_struct_0(sK4(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1285,c_39,c_38,c_37,c_63])).

cnf(c_1289,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1287])).

cnf(c_26,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1298,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_1299,plain,
    ( v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | v4_orders_2(sK4(sK6))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1301,plain,
    ( v4_orders_2(sK4(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_39,c_37])).

cnf(c_1302,plain,
    ( v1_compts_1(sK6)
    | v4_orders_2(sK4(sK6)) ),
    inference(renaming,[status(thm)],[c_1301])).

cnf(c_1303,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v4_orders_2(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_25,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK4(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1312,plain,
    ( v1_compts_1(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK4(X0))
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_38])).

cnf(c_1313,plain,
    ( v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | v7_waybel_0(sK4(sK6))
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1312])).

cnf(c_1315,plain,
    ( v7_waybel_0(sK4(sK6))
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1313,c_39,c_37])).

cnf(c_1316,plain,
    ( v1_compts_1(sK6)
    | v7_waybel_0(sK4(sK6)) ),
    inference(renaming,[status(thm)],[c_1315])).

cnf(c_1317,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v7_waybel_0(sK4(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1316])).

cnf(c_24,plain,
    ( l1_waybel_0(sK4(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1326,plain,
    ( l1_waybel_0(sK4(X0),X0)
    | v1_compts_1(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_1327,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1326])).

cnf(c_1329,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1327,c_39,c_37])).

cnf(c_1331,plain,
    ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_13096,plain,
    ( v1_compts_1(sK6) = iProver_top
    | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13071,c_1289,c_1303,c_1317,c_1331])).

cnf(c_13097,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_13096])).

cnf(c_13102,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8851,c_13097])).

cnf(c_9168,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | v4_orders_2(X0_57)
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_8090])).

cnf(c_9169,plain,
    ( m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(X0_57) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9168])).

cnf(c_9167,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | v7_waybel_0(X0_57)
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_8091])).

cnf(c_9173,plain,
    ( m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(X0_57) = iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9167])).

cnf(c_9166,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
    | l1_waybel_0(X0_57,sK6)
    | ~ l1_waybel_0(sK4(sK6),sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6)) ),
    inference(instantiation,[status(thm)],[c_8092])).

cnf(c_9177,plain,
    ( m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | l1_waybel_0(X0_57,sK6) = iProver_top
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9166])).

cnf(c_13107,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13102,c_1289,c_1303,c_1317,c_1331,c_9169,c_9173,c_9177,c_9616])).

cnf(c_13114,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8828,c_13107])).

cnf(c_2576,plain,
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
    inference(resolution_lifted,[status(thm)],[c_36,c_1947])).

cnf(c_2577,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2576])).

cnf(c_2552,plain,
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
    inference(resolution_lifted,[status(thm)],[c_36,c_1973])).

cnf(c_2553,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | v7_waybel_0(sK8(X0)) ),
    inference(unflattening,[status(thm)],[c_2552])).

cnf(c_2528,plain,
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
    inference(resolution_lifted,[status(thm)],[c_36,c_1999])).

cnf(c_2529,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2528])).

cnf(c_2504,plain,
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
    inference(resolution_lifted,[status(thm)],[c_36,c_2025])).

cnf(c_2505,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK8(X0))
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_2504])).

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
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( v3_yellow_6(sK8(X0),sK6)
    | ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_765,plain,
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

cnf(c_766,plain,
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
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_770,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_766,c_39,c_38,c_37])).

cnf(c_771,plain,
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
    inference(renaming,[status(thm)],[c_770])).

cnf(c_2759,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v4_orders_2(sK8(X0))
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2505,c_771])).

cnf(c_2770,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ v7_waybel_0(sK8(X0))
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2529,c_2759])).

cnf(c_2781,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | ~ l1_waybel_0(sK8(X0),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2553,c_2770])).

cnf(c_2787,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2577,c_2781])).

cnf(c_8088,plain,
    ( ~ l1_waybel_0(X0_57,sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,sK8(X0_57)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2787])).

cnf(c_9214,plain,
    ( ~ l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6)
    | v2_struct_0(sK4(sK6))
    | ~ v4_orders_2(sK4(sK6))
    | ~ v7_waybel_0(sK4(sK6))
    | k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8088])).

cnf(c_9215,plain,
    ( k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0
    | l1_waybel_0(sK4(sK6),sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9214])).

cnf(c_8107,plain,
    ( l1_waybel_0(sK4(sK6),sK6)
    | v1_compts_1(sK6) ),
    inference(subtyping,[status(esa)],[c_1329])).

cnf(c_8838,plain,
    ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8107])).

cnf(c_8856,plain,
    ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
    | l1_waybel_0(X1_57,sK6) != iProver_top
    | v2_struct_0(X0_57) != iProver_top
    | v2_struct_0(X1_57) = iProver_top
    | v4_orders_2(X1_57) != iProver_top
    | v7_waybel_0(X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8089])).

cnf(c_9196,plain,
    ( l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) = iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK8(X0_57)) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8828,c_8856])).

cnf(c_9278,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) != iProver_top
    | v2_struct_0(sK4(sK6)) = iProver_top
    | v4_orders_2(sK4(sK6)) != iProver_top
    | v7_waybel_0(sK4(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8838,c_9196])).

cnf(c_9509,plain,
    ( v2_struct_0(sK8(sK4(sK6))) != iProver_top
    | v1_compts_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9278,c_1289,c_1303,c_1317])).

cnf(c_9510,plain,
    ( v1_compts_1(sK6) = iProver_top
    | v2_struct_0(sK8(sK4(sK6))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9509])).

cnf(c_13256,plain,
    ( v1_compts_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13114,c_1289,c_1303,c_1317,c_1331,c_9215,c_9510])).

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
    inference(cnf_transformation,[],[f82])).

cnf(c_1254,plain,
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

cnf(c_1255,plain,
    ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1254])).

cnf(c_1259,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1255,c_39,c_37])).

cnf(c_1260,plain,
    ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1259])).

cnf(c_8111,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57))
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1260])).

cnf(c_8834,plain,
    ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57)) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8111])).

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
    inference(cnf_transformation,[],[f79])).

cnf(c_1361,plain,
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

cnf(c_1362,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1361])).

cnf(c_1366,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1362,c_39,c_37])).

cnf(c_1367,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1366])).

cnf(c_8105,plain,
    ( ~ r3_waybel_9(sK6,X0_57,X0_58)
    | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57)
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1367])).

cnf(c_8840,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57) = iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8105])).

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
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ v3_yellow_6(X0,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_732,plain,
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

cnf(c_733,plain,
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
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_737,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v1_compts_1(sK6)
    | ~ l1_waybel_0(X0,sK6)
    | ~ m2_yellow_6(X0,sK6,sK7)
    | v2_struct_0(X0)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_39,c_38,c_37])).

cnf(c_738,plain,
    ( ~ m2_yellow_6(X0,sK6,sK7)
    | ~ l1_waybel_0(X0,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_737])).

cnf(c_8112,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | ~ l1_waybel_0(X0_57,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57)
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_738])).

cnf(c_8833,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8112])).

cnf(c_34,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_49,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_50,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v4_orders_2(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v1_compts_1(sK6)
    | v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_51,plain,
    ( v1_compts_1(sK6) != iProver_top
    | v7_waybel_0(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_52,plain,
    ( l1_waybel_0(sK7,sK6) = iProver_top
    | v1_compts_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8184,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8112])).

cnf(c_8947,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | v4_orders_2(X0_57)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_8090])).

cnf(c_8948,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(X0_57) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8947])).

cnf(c_8952,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | v7_waybel_0(X0_57)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_8091])).

cnf(c_8953,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(X0_57) = iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8952])).

cnf(c_8957,plain,
    ( ~ m2_yellow_6(X0_57,sK6,sK7)
    | l1_waybel_0(X0_57,sK6)
    | ~ l1_waybel_0(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_8092])).

cnf(c_8958,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | l1_waybel_0(X0_57,sK6) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8957])).

cnf(c_9060,plain,
    ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8833,c_49,c_50,c_51,c_52,c_8184,c_8948,c_8953,c_8958])).

cnf(c_9061,plain,
    ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
    | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_9060])).

cnf(c_10039,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8840,c_9061])).

cnf(c_10585,plain,
    ( v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top
    | v1_compts_1(sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10039,c_49,c_50,c_51,c_52])).

cnf(c_10586,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10585])).

cnf(c_10038,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v2_struct_0(sK3(sK6,X0_57,X0_58)) != iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8840,c_8856])).

cnf(c_10591,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_10586,c_10038])).

cnf(c_11587,plain,
    ( v1_compts_1(sK6) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10591,c_49,c_50,c_51,c_52])).

cnf(c_11588,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
    | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_11587])).

cnf(c_11593,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
    | l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8834,c_11588])).

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
    inference(cnf_transformation,[],[f81])).

cnf(c_1636,plain,
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

cnf(c_1637,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1636])).

cnf(c_1641,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1637,c_39,c_37])).

cnf(c_1642,plain,
    ( ~ l1_waybel_0(X0,sK6)
    | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1641])).

cnf(c_8099,plain,
    ( ~ l1_waybel_0(X0_57,sK6)
    | m1_subset_1(sK5(sK6,X0_57),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1642])).

cnf(c_8936,plain,
    ( ~ l1_waybel_0(sK7,sK6)
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6))
    | ~ v1_compts_1(sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_8099])).

cnf(c_8937,plain,
    ( l1_waybel_0(sK7,sK6) != iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) = iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8936])).

cnf(c_11900,plain,
    ( v1_compts_1(sK6) != iProver_top
    | k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11593,c_49,c_50,c_51,c_52,c_8937])).

cnf(c_11901,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
    | v1_compts_1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_11900])).

cnf(c_13261,plain,
    ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13256,c_11901])).

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
    inference(cnf_transformation,[],[f80])).

cnf(c_1394,plain,
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

cnf(c_1395,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | v2_struct_0(sK6)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_1394])).

cnf(c_1399,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1395,c_39,c_37])).

cnf(c_1400,plain,
    ( ~ r3_waybel_9(sK6,X0,X1)
    | ~ l1_waybel_0(X0,sK6)
    | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK6))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1399])).

cnf(c_8104,plain,
    ( ~ r3_waybel_9(sK6,X0_57,X0_58)
    | ~ l1_waybel_0(X0_57,sK6)
    | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58)))
    | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
    | v2_struct_0(X0_57)
    | ~ v4_orders_2(X0_57)
    | ~ v7_waybel_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_1400])).

cnf(c_8841,plain,
    ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
    | l1_waybel_0(X0_57,sK6) != iProver_top
    | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
    | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(X0_57) = iProver_top
    | v4_orders_2(X0_57) != iProver_top
    | v7_waybel_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8104])).

cnf(c_13428,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) != iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top
    | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_13261,c_8841])).

cnf(c_8939,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7))
    | ~ l1_waybel_0(sK7,sK6)
    | ~ v1_compts_1(sK6)
    | v2_struct_0(sK7)
    | ~ v4_orders_2(sK7)
    | ~ v7_waybel_0(sK7) ),
    inference(instantiation,[status(thm)],[c_8111])).

cnf(c_8940,plain,
    ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) = iProver_top
    | l1_waybel_0(sK7,sK6) != iProver_top
    | v1_compts_1(sK6) != iProver_top
    | v2_struct_0(sK7) = iProver_top
    | v4_orders_2(sK7) != iProver_top
    | v7_waybel_0(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8939])).

cnf(c_13515,plain,
    ( r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13428,c_49,c_50,c_51,c_52,c_1289,c_1303,c_1317,c_1331,c_8937,c_8940,c_9215,c_9510,c_13114])).

cnf(c_13519,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_13515,c_8831])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:54:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.82/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.82/1.01  
% 3.82/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/1.01  
% 3.82/1.01  ------  iProver source info
% 3.82/1.01  
% 3.82/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.82/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/1.01  git: non_committed_changes: false
% 3.82/1.01  git: last_make_outside_of_git: false
% 3.82/1.01  
% 3.82/1.01  ------ 
% 3.82/1.01  
% 3.82/1.01  ------ Input Options
% 3.82/1.01  
% 3.82/1.01  --out_options                           all
% 3.82/1.01  --tptp_safe_out                         true
% 3.82/1.01  --problem_path                          ""
% 3.82/1.01  --include_path                          ""
% 3.82/1.01  --clausifier                            res/vclausify_rel
% 3.82/1.01  --clausifier_options                    ""
% 3.82/1.01  --stdin                                 false
% 3.82/1.01  --stats_out                             all
% 3.82/1.01  
% 3.82/1.01  ------ General Options
% 3.82/1.01  
% 3.82/1.01  --fof                                   false
% 3.82/1.01  --time_out_real                         305.
% 3.82/1.01  --time_out_virtual                      -1.
% 3.82/1.01  --symbol_type_check                     false
% 3.82/1.01  --clausify_out                          false
% 3.82/1.01  --sig_cnt_out                           false
% 3.82/1.01  --trig_cnt_out                          false
% 3.82/1.01  --trig_cnt_out_tolerance                1.
% 3.82/1.01  --trig_cnt_out_sk_spl                   false
% 3.82/1.01  --abstr_cl_out                          false
% 3.82/1.01  
% 3.82/1.01  ------ Global Options
% 3.82/1.01  
% 3.82/1.01  --schedule                              default
% 3.82/1.01  --add_important_lit                     false
% 3.82/1.01  --prop_solver_per_cl                    1000
% 3.82/1.01  --min_unsat_core                        false
% 3.82/1.01  --soft_assumptions                      false
% 3.82/1.01  --soft_lemma_size                       3
% 3.82/1.01  --prop_impl_unit_size                   0
% 3.82/1.01  --prop_impl_unit                        []
% 3.82/1.01  --share_sel_clauses                     true
% 3.82/1.01  --reset_solvers                         false
% 3.82/1.01  --bc_imp_inh                            [conj_cone]
% 3.82/1.01  --conj_cone_tolerance                   3.
% 3.82/1.01  --extra_neg_conj                        none
% 3.82/1.01  --large_theory_mode                     true
% 3.82/1.01  --prolific_symb_bound                   200
% 3.82/1.01  --lt_threshold                          2000
% 3.82/1.01  --clause_weak_htbl                      true
% 3.82/1.01  --gc_record_bc_elim                     false
% 3.82/1.01  
% 3.82/1.01  ------ Preprocessing Options
% 3.82/1.01  
% 3.82/1.01  --preprocessing_flag                    true
% 3.82/1.01  --time_out_prep_mult                    0.1
% 3.82/1.01  --splitting_mode                        input
% 3.82/1.01  --splitting_grd                         true
% 3.82/1.01  --splitting_cvd                         false
% 3.82/1.01  --splitting_cvd_svl                     false
% 3.82/1.01  --splitting_nvd                         32
% 3.82/1.01  --sub_typing                            true
% 3.82/1.01  --prep_gs_sim                           true
% 3.82/1.01  --prep_unflatten                        true
% 3.82/1.01  --prep_res_sim                          true
% 3.82/1.01  --prep_upred                            true
% 3.82/1.01  --prep_sem_filter                       exhaustive
% 3.82/1.01  --prep_sem_filter_out                   false
% 3.82/1.01  --pred_elim                             true
% 3.82/1.01  --res_sim_input                         true
% 3.82/1.01  --eq_ax_congr_red                       true
% 3.82/1.01  --pure_diseq_elim                       true
% 3.82/1.01  --brand_transform                       false
% 3.82/1.01  --non_eq_to_eq                          false
% 3.82/1.01  --prep_def_merge                        true
% 3.82/1.01  --prep_def_merge_prop_impl              false
% 3.82/1.01  --prep_def_merge_mbd                    true
% 3.82/1.01  --prep_def_merge_tr_red                 false
% 3.82/1.01  --prep_def_merge_tr_cl                  false
% 3.82/1.01  --smt_preprocessing                     true
% 3.82/1.01  --smt_ac_axioms                         fast
% 3.82/1.01  --preprocessed_out                      false
% 3.82/1.01  --preprocessed_stats                    false
% 3.82/1.01  
% 3.82/1.01  ------ Abstraction refinement Options
% 3.82/1.01  
% 3.82/1.01  --abstr_ref                             []
% 3.82/1.01  --abstr_ref_prep                        false
% 3.82/1.01  --abstr_ref_until_sat                   false
% 3.82/1.01  --abstr_ref_sig_restrict                funpre
% 3.82/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/1.01  --abstr_ref_under                       []
% 3.82/1.01  
% 3.82/1.01  ------ SAT Options
% 3.82/1.01  
% 3.82/1.01  --sat_mode                              false
% 3.82/1.01  --sat_fm_restart_options                ""
% 3.82/1.01  --sat_gr_def                            false
% 3.82/1.01  --sat_epr_types                         true
% 3.82/1.01  --sat_non_cyclic_types                  false
% 3.82/1.01  --sat_finite_models                     false
% 3.82/1.01  --sat_fm_lemmas                         false
% 3.82/1.01  --sat_fm_prep                           false
% 3.82/1.01  --sat_fm_uc_incr                        true
% 3.82/1.01  --sat_out_model                         small
% 3.82/1.01  --sat_out_clauses                       false
% 3.82/1.01  
% 3.82/1.01  ------ QBF Options
% 3.82/1.01  
% 3.82/1.01  --qbf_mode                              false
% 3.82/1.01  --qbf_elim_univ                         false
% 3.82/1.01  --qbf_dom_inst                          none
% 3.82/1.01  --qbf_dom_pre_inst                      false
% 3.82/1.01  --qbf_sk_in                             false
% 3.82/1.01  --qbf_pred_elim                         true
% 3.82/1.01  --qbf_split                             512
% 3.82/1.01  
% 3.82/1.01  ------ BMC1 Options
% 3.82/1.01  
% 3.82/1.01  --bmc1_incremental                      false
% 3.82/1.01  --bmc1_axioms                           reachable_all
% 3.82/1.01  --bmc1_min_bound                        0
% 3.82/1.01  --bmc1_max_bound                        -1
% 3.82/1.01  --bmc1_max_bound_default                -1
% 3.82/1.01  --bmc1_symbol_reachability              true
% 3.82/1.01  --bmc1_property_lemmas                  false
% 3.82/1.01  --bmc1_k_induction                      false
% 3.82/1.01  --bmc1_non_equiv_states                 false
% 3.82/1.01  --bmc1_deadlock                         false
% 3.82/1.01  --bmc1_ucm                              false
% 3.82/1.01  --bmc1_add_unsat_core                   none
% 3.82/1.01  --bmc1_unsat_core_children              false
% 3.82/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/1.01  --bmc1_out_stat                         full
% 3.82/1.01  --bmc1_ground_init                      false
% 3.82/1.01  --bmc1_pre_inst_next_state              false
% 3.82/1.01  --bmc1_pre_inst_state                   false
% 3.82/1.01  --bmc1_pre_inst_reach_state             false
% 3.82/1.01  --bmc1_out_unsat_core                   false
% 3.82/1.01  --bmc1_aig_witness_out                  false
% 3.82/1.01  --bmc1_verbose                          false
% 3.82/1.01  --bmc1_dump_clauses_tptp                false
% 3.82/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.82/1.01  --bmc1_dump_file                        -
% 3.82/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.82/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.82/1.01  --bmc1_ucm_extend_mode                  1
% 3.82/1.01  --bmc1_ucm_init_mode                    2
% 3.82/1.01  --bmc1_ucm_cone_mode                    none
% 3.82/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.82/1.01  --bmc1_ucm_relax_model                  4
% 3.82/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.82/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/1.01  --bmc1_ucm_layered_model                none
% 3.82/1.01  --bmc1_ucm_max_lemma_size               10
% 3.82/1.01  
% 3.82/1.01  ------ AIG Options
% 3.82/1.01  
% 3.82/1.01  --aig_mode                              false
% 3.82/1.01  
% 3.82/1.01  ------ Instantiation Options
% 3.82/1.01  
% 3.82/1.01  --instantiation_flag                    true
% 3.82/1.01  --inst_sos_flag                         true
% 3.82/1.01  --inst_sos_phase                        true
% 3.82/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/1.01  --inst_lit_sel_side                     num_symb
% 3.82/1.01  --inst_solver_per_active                1400
% 3.82/1.01  --inst_solver_calls_frac                1.
% 3.82/1.01  --inst_passive_queue_type               priority_queues
% 3.82/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/1.01  --inst_passive_queues_freq              [25;2]
% 3.82/1.01  --inst_dismatching                      true
% 3.82/1.01  --inst_eager_unprocessed_to_passive     true
% 3.82/1.01  --inst_prop_sim_given                   true
% 3.82/1.01  --inst_prop_sim_new                     false
% 3.82/1.01  --inst_subs_new                         false
% 3.82/1.01  --inst_eq_res_simp                      false
% 3.82/1.01  --inst_subs_given                       false
% 3.82/1.01  --inst_orphan_elimination               true
% 3.82/1.01  --inst_learning_loop_flag               true
% 3.82/1.01  --inst_learning_start                   3000
% 3.82/1.01  --inst_learning_factor                  2
% 3.82/1.01  --inst_start_prop_sim_after_learn       3
% 3.82/1.01  --inst_sel_renew                        solver
% 3.82/1.01  --inst_lit_activity_flag                true
% 3.82/1.01  --inst_restr_to_given                   false
% 3.82/1.01  --inst_activity_threshold               500
% 3.82/1.01  --inst_out_proof                        true
% 3.82/1.01  
% 3.82/1.01  ------ Resolution Options
% 3.82/1.01  
% 3.82/1.01  --resolution_flag                       true
% 3.82/1.01  --res_lit_sel                           adaptive
% 3.82/1.01  --res_lit_sel_side                      none
% 3.82/1.01  --res_ordering                          kbo
% 3.82/1.01  --res_to_prop_solver                    active
% 3.82/1.01  --res_prop_simpl_new                    false
% 3.82/1.01  --res_prop_simpl_given                  true
% 3.82/1.01  --res_passive_queue_type                priority_queues
% 3.82/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/1.01  --res_passive_queues_freq               [15;5]
% 3.82/1.01  --res_forward_subs                      full
% 3.82/1.01  --res_backward_subs                     full
% 3.82/1.01  --res_forward_subs_resolution           true
% 3.82/1.01  --res_backward_subs_resolution          true
% 3.82/1.01  --res_orphan_elimination                true
% 3.82/1.01  --res_time_limit                        2.
% 3.82/1.01  --res_out_proof                         true
% 3.82/1.01  
% 3.82/1.01  ------ Superposition Options
% 3.82/1.01  
% 3.82/1.01  --superposition_flag                    true
% 3.82/1.01  --sup_passive_queue_type                priority_queues
% 3.82/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.82/1.01  --demod_completeness_check              fast
% 3.82/1.01  --demod_use_ground                      true
% 3.82/1.01  --sup_to_prop_solver                    passive
% 3.82/1.01  --sup_prop_simpl_new                    true
% 3.82/1.01  --sup_prop_simpl_given                  true
% 3.82/1.01  --sup_fun_splitting                     true
% 3.82/1.01  --sup_smt_interval                      50000
% 3.82/1.01  
% 3.82/1.01  ------ Superposition Simplification Setup
% 3.82/1.01  
% 3.82/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.82/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.82/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.82/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.82/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.82/1.01  --sup_immed_triv                        [TrivRules]
% 3.82/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.01  --sup_immed_bw_main                     []
% 3.82/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.82/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.01  --sup_input_bw                          []
% 3.82/1.01  
% 3.82/1.01  ------ Combination Options
% 3.82/1.01  
% 3.82/1.01  --comb_res_mult                         3
% 3.82/1.01  --comb_sup_mult                         2
% 3.82/1.01  --comb_inst_mult                        10
% 3.82/1.01  
% 3.82/1.01  ------ Debug Options
% 3.82/1.01  
% 3.82/1.01  --dbg_backtrace                         false
% 3.82/1.01  --dbg_dump_prop_clauses                 false
% 3.82/1.01  --dbg_dump_prop_clauses_file            -
% 3.82/1.01  --dbg_out_stat                          false
% 3.82/1.01  ------ Parsing...
% 3.82/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/1.01  
% 3.82/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.82/1.01  
% 3.82/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/1.01  
% 3.82/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/1.01  ------ Proving...
% 3.82/1.01  ------ Problem Properties 
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  clauses                                 34
% 3.82/1.01  conjectures                             6
% 3.82/1.01  EPR                                     10
% 3.82/1.01  Horn                                    11
% 3.82/1.01  unary                                   3
% 3.82/1.01  binary                                  9
% 3.82/1.01  lits                                    167
% 3.82/1.01  lits eq                                 6
% 3.82/1.01  fd_pure                                 0
% 3.82/1.01  fd_pseudo                               0
% 3.82/1.01  fd_cond                                 0
% 3.82/1.01  fd_pseudo_cond                          4
% 3.82/1.01  AC symbols                              0
% 3.82/1.01  
% 3.82/1.01  ------ Schedule dynamic 5 is on 
% 3.82/1.01  
% 3.82/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  ------ 
% 3.82/1.01  Current options:
% 3.82/1.01  ------ 
% 3.82/1.01  
% 3.82/1.01  ------ Input Options
% 3.82/1.01  
% 3.82/1.01  --out_options                           all
% 3.82/1.01  --tptp_safe_out                         true
% 3.82/1.01  --problem_path                          ""
% 3.82/1.01  --include_path                          ""
% 3.82/1.01  --clausifier                            res/vclausify_rel
% 3.82/1.01  --clausifier_options                    ""
% 3.82/1.01  --stdin                                 false
% 3.82/1.01  --stats_out                             all
% 3.82/1.01  
% 3.82/1.01  ------ General Options
% 3.82/1.01  
% 3.82/1.01  --fof                                   false
% 3.82/1.01  --time_out_real                         305.
% 3.82/1.01  --time_out_virtual                      -1.
% 3.82/1.01  --symbol_type_check                     false
% 3.82/1.01  --clausify_out                          false
% 3.82/1.01  --sig_cnt_out                           false
% 3.82/1.01  --trig_cnt_out                          false
% 3.82/1.01  --trig_cnt_out_tolerance                1.
% 3.82/1.01  --trig_cnt_out_sk_spl                   false
% 3.82/1.01  --abstr_cl_out                          false
% 3.82/1.01  
% 3.82/1.01  ------ Global Options
% 3.82/1.01  
% 3.82/1.01  --schedule                              default
% 3.82/1.01  --add_important_lit                     false
% 3.82/1.01  --prop_solver_per_cl                    1000
% 3.82/1.01  --min_unsat_core                        false
% 3.82/1.01  --soft_assumptions                      false
% 3.82/1.01  --soft_lemma_size                       3
% 3.82/1.01  --prop_impl_unit_size                   0
% 3.82/1.01  --prop_impl_unit                        []
% 3.82/1.01  --share_sel_clauses                     true
% 3.82/1.01  --reset_solvers                         false
% 3.82/1.01  --bc_imp_inh                            [conj_cone]
% 3.82/1.01  --conj_cone_tolerance                   3.
% 3.82/1.01  --extra_neg_conj                        none
% 3.82/1.01  --large_theory_mode                     true
% 3.82/1.01  --prolific_symb_bound                   200
% 3.82/1.01  --lt_threshold                          2000
% 3.82/1.01  --clause_weak_htbl                      true
% 3.82/1.01  --gc_record_bc_elim                     false
% 3.82/1.01  
% 3.82/1.01  ------ Preprocessing Options
% 3.82/1.01  
% 3.82/1.01  --preprocessing_flag                    true
% 3.82/1.01  --time_out_prep_mult                    0.1
% 3.82/1.01  --splitting_mode                        input
% 3.82/1.01  --splitting_grd                         true
% 3.82/1.01  --splitting_cvd                         false
% 3.82/1.01  --splitting_cvd_svl                     false
% 3.82/1.01  --splitting_nvd                         32
% 3.82/1.01  --sub_typing                            true
% 3.82/1.01  --prep_gs_sim                           true
% 3.82/1.01  --prep_unflatten                        true
% 3.82/1.01  --prep_res_sim                          true
% 3.82/1.01  --prep_upred                            true
% 3.82/1.01  --prep_sem_filter                       exhaustive
% 3.82/1.01  --prep_sem_filter_out                   false
% 3.82/1.01  --pred_elim                             true
% 3.82/1.01  --res_sim_input                         true
% 3.82/1.01  --eq_ax_congr_red                       true
% 3.82/1.01  --pure_diseq_elim                       true
% 3.82/1.01  --brand_transform                       false
% 3.82/1.01  --non_eq_to_eq                          false
% 3.82/1.01  --prep_def_merge                        true
% 3.82/1.01  --prep_def_merge_prop_impl              false
% 3.82/1.01  --prep_def_merge_mbd                    true
% 3.82/1.01  --prep_def_merge_tr_red                 false
% 3.82/1.01  --prep_def_merge_tr_cl                  false
% 3.82/1.01  --smt_preprocessing                     true
% 3.82/1.01  --smt_ac_axioms                         fast
% 3.82/1.01  --preprocessed_out                      false
% 3.82/1.01  --preprocessed_stats                    false
% 3.82/1.01  
% 3.82/1.01  ------ Abstraction refinement Options
% 3.82/1.01  
% 3.82/1.01  --abstr_ref                             []
% 3.82/1.01  --abstr_ref_prep                        false
% 3.82/1.01  --abstr_ref_until_sat                   false
% 3.82/1.01  --abstr_ref_sig_restrict                funpre
% 3.82/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.82/1.01  --abstr_ref_under                       []
% 3.82/1.01  
% 3.82/1.01  ------ SAT Options
% 3.82/1.01  
% 3.82/1.01  --sat_mode                              false
% 3.82/1.01  --sat_fm_restart_options                ""
% 3.82/1.01  --sat_gr_def                            false
% 3.82/1.01  --sat_epr_types                         true
% 3.82/1.01  --sat_non_cyclic_types                  false
% 3.82/1.01  --sat_finite_models                     false
% 3.82/1.01  --sat_fm_lemmas                         false
% 3.82/1.01  --sat_fm_prep                           false
% 3.82/1.01  --sat_fm_uc_incr                        true
% 3.82/1.01  --sat_out_model                         small
% 3.82/1.01  --sat_out_clauses                       false
% 3.82/1.01  
% 3.82/1.01  ------ QBF Options
% 3.82/1.01  
% 3.82/1.01  --qbf_mode                              false
% 3.82/1.01  --qbf_elim_univ                         false
% 3.82/1.01  --qbf_dom_inst                          none
% 3.82/1.01  --qbf_dom_pre_inst                      false
% 3.82/1.01  --qbf_sk_in                             false
% 3.82/1.01  --qbf_pred_elim                         true
% 3.82/1.01  --qbf_split                             512
% 3.82/1.01  
% 3.82/1.01  ------ BMC1 Options
% 3.82/1.01  
% 3.82/1.01  --bmc1_incremental                      false
% 3.82/1.01  --bmc1_axioms                           reachable_all
% 3.82/1.01  --bmc1_min_bound                        0
% 3.82/1.01  --bmc1_max_bound                        -1
% 3.82/1.01  --bmc1_max_bound_default                -1
% 3.82/1.01  --bmc1_symbol_reachability              true
% 3.82/1.01  --bmc1_property_lemmas                  false
% 3.82/1.01  --bmc1_k_induction                      false
% 3.82/1.01  --bmc1_non_equiv_states                 false
% 3.82/1.01  --bmc1_deadlock                         false
% 3.82/1.01  --bmc1_ucm                              false
% 3.82/1.01  --bmc1_add_unsat_core                   none
% 3.82/1.01  --bmc1_unsat_core_children              false
% 3.82/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.82/1.01  --bmc1_out_stat                         full
% 3.82/1.01  --bmc1_ground_init                      false
% 3.82/1.01  --bmc1_pre_inst_next_state              false
% 3.82/1.01  --bmc1_pre_inst_state                   false
% 3.82/1.01  --bmc1_pre_inst_reach_state             false
% 3.82/1.01  --bmc1_out_unsat_core                   false
% 3.82/1.01  --bmc1_aig_witness_out                  false
% 3.82/1.01  --bmc1_verbose                          false
% 3.82/1.01  --bmc1_dump_clauses_tptp                false
% 3.82/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.82/1.01  --bmc1_dump_file                        -
% 3.82/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.82/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.82/1.01  --bmc1_ucm_extend_mode                  1
% 3.82/1.01  --bmc1_ucm_init_mode                    2
% 3.82/1.01  --bmc1_ucm_cone_mode                    none
% 3.82/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.82/1.01  --bmc1_ucm_relax_model                  4
% 3.82/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.82/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.82/1.01  --bmc1_ucm_layered_model                none
% 3.82/1.01  --bmc1_ucm_max_lemma_size               10
% 3.82/1.01  
% 3.82/1.01  ------ AIG Options
% 3.82/1.01  
% 3.82/1.01  --aig_mode                              false
% 3.82/1.01  
% 3.82/1.01  ------ Instantiation Options
% 3.82/1.01  
% 3.82/1.01  --instantiation_flag                    true
% 3.82/1.01  --inst_sos_flag                         true
% 3.82/1.01  --inst_sos_phase                        true
% 3.82/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.82/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.82/1.01  --inst_lit_sel_side                     none
% 3.82/1.01  --inst_solver_per_active                1400
% 3.82/1.01  --inst_solver_calls_frac                1.
% 3.82/1.01  --inst_passive_queue_type               priority_queues
% 3.82/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.82/1.01  --inst_passive_queues_freq              [25;2]
% 3.82/1.01  --inst_dismatching                      true
% 3.82/1.01  --inst_eager_unprocessed_to_passive     true
% 3.82/1.01  --inst_prop_sim_given                   true
% 3.82/1.01  --inst_prop_sim_new                     false
% 3.82/1.01  --inst_subs_new                         false
% 3.82/1.01  --inst_eq_res_simp                      false
% 3.82/1.01  --inst_subs_given                       false
% 3.82/1.01  --inst_orphan_elimination               true
% 3.82/1.01  --inst_learning_loop_flag               true
% 3.82/1.01  --inst_learning_start                   3000
% 3.82/1.01  --inst_learning_factor                  2
% 3.82/1.01  --inst_start_prop_sim_after_learn       3
% 3.82/1.01  --inst_sel_renew                        solver
% 3.82/1.01  --inst_lit_activity_flag                true
% 3.82/1.01  --inst_restr_to_given                   false
% 3.82/1.01  --inst_activity_threshold               500
% 3.82/1.01  --inst_out_proof                        true
% 3.82/1.01  
% 3.82/1.01  ------ Resolution Options
% 3.82/1.01  
% 3.82/1.01  --resolution_flag                       false
% 3.82/1.01  --res_lit_sel                           adaptive
% 3.82/1.01  --res_lit_sel_side                      none
% 3.82/1.01  --res_ordering                          kbo
% 3.82/1.01  --res_to_prop_solver                    active
% 3.82/1.01  --res_prop_simpl_new                    false
% 3.82/1.01  --res_prop_simpl_given                  true
% 3.82/1.01  --res_passive_queue_type                priority_queues
% 3.82/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.82/1.01  --res_passive_queues_freq               [15;5]
% 3.82/1.01  --res_forward_subs                      full
% 3.82/1.01  --res_backward_subs                     full
% 3.82/1.01  --res_forward_subs_resolution           true
% 3.82/1.01  --res_backward_subs_resolution          true
% 3.82/1.01  --res_orphan_elimination                true
% 3.82/1.01  --res_time_limit                        2.
% 3.82/1.01  --res_out_proof                         true
% 3.82/1.01  
% 3.82/1.01  ------ Superposition Options
% 3.82/1.01  
% 3.82/1.01  --superposition_flag                    true
% 3.82/1.01  --sup_passive_queue_type                priority_queues
% 3.82/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.82/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.82/1.01  --demod_completeness_check              fast
% 3.82/1.01  --demod_use_ground                      true
% 3.82/1.01  --sup_to_prop_solver                    passive
% 3.82/1.01  --sup_prop_simpl_new                    true
% 3.82/1.01  --sup_prop_simpl_given                  true
% 3.82/1.01  --sup_fun_splitting                     true
% 3.82/1.01  --sup_smt_interval                      50000
% 3.82/1.01  
% 3.82/1.01  ------ Superposition Simplification Setup
% 3.82/1.01  
% 3.82/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.82/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.82/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.82/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.82/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.82/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.82/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.82/1.01  --sup_immed_triv                        [TrivRules]
% 3.82/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.01  --sup_immed_bw_main                     []
% 3.82/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.82/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.82/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.82/1.01  --sup_input_bw                          []
% 3.82/1.01  
% 3.82/1.01  ------ Combination Options
% 3.82/1.01  
% 3.82/1.01  --comb_res_mult                         3
% 3.82/1.01  --comb_sup_mult                         2
% 3.82/1.01  --comb_inst_mult                        10
% 3.82/1.01  
% 3.82/1.01  ------ Debug Options
% 3.82/1.01  
% 3.82/1.01  --dbg_backtrace                         false
% 3.82/1.01  --dbg_dump_prop_clauses                 false
% 3.82/1.01  --dbg_dump_prop_clauses_file            -
% 3.82/1.01  --dbg_out_stat                          false
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  ------ Proving...
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  % SZS status Theorem for theBenchmark.p
% 3.82/1.01  
% 3.82/1.01   Resolution empty clause
% 3.82/1.01  
% 3.82/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/1.01  
% 3.82/1.01  fof(f13,conjecture,(
% 3.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f14,negated_conjecture,(
% 3.82/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 3.82/1.01    inference(negated_conjecture,[],[f13])).
% 3.82/1.01  
% 3.82/1.01  fof(f33,plain,(
% 3.82/1.01    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f14])).
% 3.82/1.01  
% 3.82/1.01  fof(f34,plain,(
% 3.82/1.01    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f33])).
% 3.82/1.01  
% 3.82/1.01  fof(f51,plain,(
% 3.82/1.01    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.82/1.01    inference(nnf_transformation,[],[f34])).
% 3.82/1.01  
% 3.82/1.01  fof(f52,plain,(
% 3.82/1.01    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f51])).
% 3.82/1.01  
% 3.82/1.01  fof(f53,plain,(
% 3.82/1.01    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.82/1.01    inference(rectify,[],[f52])).
% 3.82/1.01  
% 3.82/1.01  fof(f56,plain,(
% 3.82/1.01    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK8(X3),X0) & m2_yellow_6(sK8(X3),X0,X3)))) )),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f55,plain,(
% 3.82/1.01    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK7)) & l1_waybel_0(sK7,X0) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7))) )),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f54,plain,(
% 3.82/1.01    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,X1)) & l1_waybel_0(X1,sK6) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK6)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK6) & m2_yellow_6(X4,sK6,X3)) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK6)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f57,plain,(
% 3.82/1.01    ((! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,sK7)) & l1_waybel_0(sK7,sK6) & v7_waybel_0(sK7) & v4_orders_2(sK7) & ~v2_struct_0(sK7)) | ~v1_compts_1(sK6)) & (! [X3] : ((v3_yellow_6(sK8(X3),sK6) & m2_yellow_6(sK8(X3),sK6,X3)) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK6)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 3.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f53,f56,f55,f54])).
% 3.82/1.01  
% 3.82/1.01  fof(f91,plain,(
% 3.82/1.01    ( ! [X3] : (m2_yellow_6(sK8(X3),sK6,X3) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK6)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f5,axiom,(
% 3.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f17,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f5])).
% 3.82/1.01  
% 3.82/1.01  fof(f18,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f17])).
% 3.82/1.01  
% 3.82/1.01  fof(f36,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(nnf_transformation,[],[f18])).
% 3.82/1.01  
% 3.82/1.01  fof(f37,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f36])).
% 3.82/1.01  
% 3.82/1.01  fof(f38,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(rectify,[],[f37])).
% 3.82/1.01  
% 3.82/1.01  fof(f41,plain,(
% 3.82/1.01    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6)))),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f40,plain,(
% 3.82/1.01    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X3)))) )),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f39,plain,(
% 3.82/1.01    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f42,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).
% 3.82/1.01  
% 3.82/1.01  fof(f66,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f42])).
% 3.82/1.01  
% 3.82/1.01  fof(f89,plain,(
% 3.82/1.01    v2_pre_topc(sK6)),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f88,plain,(
% 3.82/1.01    ~v2_struct_0(sK6)),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f90,plain,(
% 3.82/1.01    l1_pre_topc(sK6)),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f6,axiom,(
% 3.82/1.01    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f19,plain,(
% 3.82/1.01    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f6])).
% 3.82/1.01  
% 3.82/1.01  fof(f20,plain,(
% 3.82/1.01    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f19])).
% 3.82/1.01  
% 3.82/1.01  fof(f70,plain,(
% 3.82/1.01    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f20])).
% 3.82/1.01  
% 3.82/1.01  fof(f64,plain,(
% 3.82/1.01    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f42])).
% 3.82/1.01  
% 3.82/1.01  fof(f99,plain,(
% 3.82/1.01    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(equality_resolution,[],[f64])).
% 3.82/1.01  
% 3.82/1.01  fof(f67,plain,(
% 3.82/1.01    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2)) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f42])).
% 3.82/1.01  
% 3.82/1.01  fof(f1,axiom,(
% 3.82/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f58,plain,(
% 3.82/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f1])).
% 3.82/1.01  
% 3.82/1.01  fof(f3,axiom,(
% 3.82/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f15,plain,(
% 3.82/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.82/1.01    inference(ennf_transformation,[],[f3])).
% 3.82/1.01  
% 3.82/1.01  fof(f61,plain,(
% 3.82/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f15])).
% 3.82/1.01  
% 3.82/1.01  fof(f2,axiom,(
% 3.82/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f35,plain,(
% 3.82/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.82/1.01    inference(nnf_transformation,[],[f2])).
% 3.82/1.01  
% 3.82/1.01  fof(f60,plain,(
% 3.82/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f35])).
% 3.82/1.01  
% 3.82/1.01  fof(f65,plain,(
% 3.82/1.01    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f42])).
% 3.82/1.01  
% 3.82/1.01  fof(f98,plain,(
% 3.82/1.01    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(equality_resolution,[],[f65])).
% 3.82/1.01  
% 3.82/1.01  fof(f9,axiom,(
% 3.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f25,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f9])).
% 3.82/1.01  
% 3.82/1.01  fof(f26,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f25])).
% 3.82/1.01  
% 3.82/1.01  fof(f77,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f26])).
% 3.82/1.01  
% 3.82/1.01  fof(f10,axiom,(
% 3.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_waybel_9(X0,X2,X3) => r3_waybel_9(X0,X1,X3))))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f27,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f10])).
% 3.82/1.01  
% 3.82/1.01  fof(f28,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f27])).
% 3.82/1.01  
% 3.82/1.01  fof(f78,plain,(
% 3.82/1.01    ( ! [X2,X0,X3,X1] : (r3_waybel_9(X0,X1,X3) | ~r3_waybel_9(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f28])).
% 3.82/1.01  
% 3.82/1.01  fof(f4,axiom,(
% 3.82/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f16,plain,(
% 3.82/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.82/1.01    inference(ennf_transformation,[],[f4])).
% 3.82/1.01  
% 3.82/1.01  fof(f62,plain,(
% 3.82/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f16])).
% 3.82/1.01  
% 3.82/1.01  fof(f7,axiom,(
% 3.82/1.01    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f21,plain,(
% 3.82/1.01    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f7])).
% 3.82/1.01  
% 3.82/1.01  fof(f22,plain,(
% 3.82/1.01    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f21])).
% 3.82/1.01  
% 3.82/1.01  fof(f74,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f22])).
% 3.82/1.01  
% 3.82/1.01  fof(f73,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f22])).
% 3.82/1.01  
% 3.82/1.01  fof(f72,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f22])).
% 3.82/1.01  
% 3.82/1.01  fof(f71,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f22])).
% 3.82/1.01  
% 3.82/1.01  fof(f12,axiom,(
% 3.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f31,plain,(
% 3.82/1.01    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f12])).
% 3.82/1.01  
% 3.82/1.01  fof(f32,plain,(
% 3.82/1.01    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f31])).
% 3.82/1.01  
% 3.82/1.01  fof(f46,plain,(
% 3.82/1.01    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(nnf_transformation,[],[f32])).
% 3.82/1.01  
% 3.82/1.01  fof(f47,plain,(
% 3.82/1.01    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(rectify,[],[f46])).
% 3.82/1.01  
% 3.82/1.01  fof(f49,plain,(
% 3.82/1.01    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))))),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f48,plain,(
% 3.82/1.01    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0))))),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f50,plain,(
% 3.82/1.01    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK4(X0),X0) & v7_waybel_0(sK4(X0)) & v4_orders_2(sK4(X0)) & ~v2_struct_0(sK4(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK5(X0,X3)) & m1_subset_1(sK5(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).
% 3.82/1.01  
% 3.82/1.01  fof(f87,plain,(
% 3.82/1.01    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK4(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f50])).
% 3.82/1.01  
% 3.82/1.01  fof(f83,plain,(
% 3.82/1.01    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f50])).
% 3.82/1.01  
% 3.82/1.01  fof(f84,plain,(
% 3.82/1.01    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f50])).
% 3.82/1.01  
% 3.82/1.01  fof(f85,plain,(
% 3.82/1.01    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK4(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f50])).
% 3.82/1.01  
% 3.82/1.01  fof(f86,plain,(
% 3.82/1.01    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK4(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f50])).
% 3.82/1.01  
% 3.82/1.01  fof(f8,axiom,(
% 3.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f23,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f8])).
% 3.82/1.01  
% 3.82/1.01  fof(f24,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f23])).
% 3.82/1.01  
% 3.82/1.01  fof(f43,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(nnf_transformation,[],[f24])).
% 3.82/1.01  
% 3.82/1.01  fof(f75,plain,(
% 3.82/1.01    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f43])).
% 3.82/1.01  
% 3.82/1.01  fof(f92,plain,(
% 3.82/1.01    ( ! [X3] : (v3_yellow_6(sK8(X3),sK6) | ~l1_waybel_0(X3,sK6) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK6)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f82,plain,(
% 3.82/1.01    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK5(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f50])).
% 3.82/1.01  
% 3.82/1.01  fof(f11,axiom,(
% 3.82/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 3.82/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.82/1.01  
% 3.82/1.01  fof(f29,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.82/1.01    inference(ennf_transformation,[],[f11])).
% 3.82/1.01  
% 3.82/1.01  fof(f30,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(flattening,[],[f29])).
% 3.82/1.01  
% 3.82/1.01  fof(f44,plain,(
% 3.82/1.01    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)))),
% 3.82/1.01    introduced(choice_axiom,[])).
% 3.82/1.01  
% 3.82/1.01  fof(f45,plain,(
% 3.82/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) & m2_yellow_6(sK3(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.82/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f44])).
% 3.82/1.01  
% 3.82/1.01  fof(f79,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (m2_yellow_6(sK3(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f45])).
% 3.82/1.01  
% 3.82/1.01  fof(f76,plain,(
% 3.82/1.01    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f43])).
% 3.82/1.01  
% 3.82/1.01  fof(f97,plain,(
% 3.82/1.01    ( ! [X2] : (~v3_yellow_6(X2,sK6) | ~m2_yellow_6(X2,sK6,sK7) | ~v1_compts_1(sK6)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f93,plain,(
% 3.82/1.01    ~v2_struct_0(sK7) | ~v1_compts_1(sK6)),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f94,plain,(
% 3.82/1.01    v4_orders_2(sK7) | ~v1_compts_1(sK6)),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f95,plain,(
% 3.82/1.01    v7_waybel_0(sK7) | ~v1_compts_1(sK6)),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f96,plain,(
% 3.82/1.01    l1_waybel_0(sK7,sK6) | ~v1_compts_1(sK6)),
% 3.82/1.01    inference(cnf_transformation,[],[f57])).
% 3.82/1.01  
% 3.82/1.01  fof(f81,plain,(
% 3.82/1.01    ( ! [X0,X3] : (m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f50])).
% 3.82/1.01  
% 3.82/1.01  fof(f80,plain,(
% 3.82/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.82/1.01    inference(cnf_transformation,[],[f45])).
% 3.82/1.01  
% 3.82/1.01  cnf(c_36,negated_conjecture,
% 3.82/1.01      ( m2_yellow_6(sK8(X0),sK6,X0)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8117,negated_conjecture,
% 3.82/1.01      ( m2_yellow_6(sK8(X0_57),sK6,X0_57)
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_36]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8828,plain,
% 3.82/1.01      ( m2_yellow_6(sK8(X0_57),sK6,X0_57) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8117]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.01      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 3.82/1.01      | ~ v2_pre_topc(X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | k10_yellow_6(X1,X0) = X2 ),
% 3.82/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_38,negated_conjecture,
% 3.82/1.01      ( v2_pre_topc(sK6) ),
% 3.82/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1741,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.01      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | k10_yellow_6(X1,X0) = X2
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1742,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6)
% 3.82/1.01      | k10_yellow_6(sK6,X0) = X1 ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1741]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_39,negated_conjecture,
% 3.82/1.01      ( ~ v2_struct_0(sK6) ),
% 3.82/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_37,negated_conjecture,
% 3.82/1.01      ( l1_pre_topc(sK6) ),
% 3.82/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1746,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | k10_yellow_6(sK6,X0) = X1 ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1742,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1747,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0,X1),u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | k10_yellow_6(sK6,X0) = X1 ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1746]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8094,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57)
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = X0_58 ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1747]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8851,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = X0_58
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6)) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8094]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_12,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.01      | ~ v2_pre_topc(X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1) ),
% 3.82/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1666,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1667,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1666]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1671,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1667,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1672,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1671]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10,plain,
% 3.82/1.01      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1492,plain,
% 3.82/1.01      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1493,plain,
% 3.82/1.01      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1492]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1497,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1493,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1498,plain,
% 3.82/1.01      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1497]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1689,plain,
% 3.82/1.01      ( m1_connsp_2(sK2(sK6,X0,X1),sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1672,c_1498]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8097,plain,
% 3.82/1.01      ( m1_connsp_2(sK2(sK6,X0_57,X0_58),sK6,X0_58)
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
% 3.82/1.01      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1689]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8848,plain,
% 3.82/1.01      ( m1_connsp_2(sK2(sK6,X0_57,X0_58),sK6,X0_58) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57)) = iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8097]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_7,plain,
% 3.82/1.01      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 3.82/1.01      | r1_waybel_0(X1,X2,X0)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | r2_hidden(sK0(X1,X2,X3),X3)
% 3.82/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.01      | ~ v2_pre_topc(X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | k10_yellow_6(X1,X2) = X3 ),
% 3.82/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1774,plain,
% 3.82/1.01      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 3.82/1.01      | r1_waybel_0(X1,X2,X0)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | r2_hidden(sK0(X1,X2,X3),X3)
% 3.82/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | k10_yellow_6(X1,X2) = X3
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1775,plain,
% 3.82/1.01      ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.82/1.01      | r1_waybel_0(sK6,X1,X0)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(sK6)
% 3.82/1.01      | k10_yellow_6(sK6,X1) = X2 ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1774]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1779,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.82/1.01      | r1_waybel_0(sK6,X1,X0)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | k10_yellow_6(sK6,X1) = X2 ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1775,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1780,plain,
% 3.82/1.01      ( ~ m1_connsp_2(X0,sK6,sK0(sK6,X1,X2))
% 3.82/1.01      | r1_waybel_0(sK6,X1,X0)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | r2_hidden(sK0(sK6,X1,X2),X2)
% 3.82/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | k10_yellow_6(sK6,X1) = X2 ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1779]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8093,plain,
% 3.82/1.01      ( ~ m1_connsp_2(X0_59,sK6,sK0(sK6,X0_57,X0_58))
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,X0_59)
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58)
% 3.82/1.01      | ~ m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57)
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = X0_58 ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1780]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8852,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = X0_58
% 3.82/1.01      | m1_connsp_2(X0_59,sK6,sK0(sK6,X0_57,X0_58)) != iProver_top
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,X0_59) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8093]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10522,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = X0_58
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,X0_58))) = iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),k10_yellow_6(sK6,X1_57)) = iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8848,c_8852]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8222,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = X0_58
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,X0_58),u1_struct_0(sK6)) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8094]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10860,plain,
% 3.82/1.01      ( m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),k10_yellow_6(sK6,X1_57)) = iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,X0_58))) = iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = X0_58
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_10522,c_8222]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10861,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = X0_58
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,X0_58))) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),X0_58) = iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,X0_58),k10_yellow_6(sK6,X1_57)) = iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_10860]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_0,plain,
% 3.82/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_3,plain,
% 3.82/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_555,plain,
% 3.82/1.01      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_556,plain,
% 3.82/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_555]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8114,plain,
% 3.82/1.01      ( ~ r2_hidden(X0_58,k1_xboole_0) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_556]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8831,plain,
% 3.82/1.01      ( r2_hidden(X0_58,k1_xboole_0) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8114]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10868,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0))) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X1_57)) = iProver_top
% 3.82/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_10861,c_8831]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1,plain,
% 3.82/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.82/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_306,plain,
% 3.82/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.82/1.01      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_307,plain,
% 3.82/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_306]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_546,plain,
% 3.82/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | X1 != X2 | k1_xboole_0 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_307]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_547,plain,
% 3.82/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_546]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8115,plain,
% 3.82/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_58)) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_547]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9615,plain,
% 3.82/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8115]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9616,plain,
% 3.82/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_9615]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10883,plain,
% 3.82/1.01      ( r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X1_57)) = iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0))) = iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_10868,c_9616]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10884,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | r1_waybel_0(sK6,X0_57,sK2(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0))) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X1_57)) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_10883]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9,plain,
% 3.82/1.01      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1528,plain,
% 3.82/1.01      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1529,plain,
% 3.82/1.01      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1528]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1533,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1529,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1534,plain,
% 3.82/1.01      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | ~ m1_subset_1(k10_yellow_6(sK6,X0),k1_zfmisc_1(u1_struct_0(sK6)))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1533]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1690,plain,
% 3.82/1.01      ( ~ r1_waybel_0(sK6,X0,sK2(sK6,X0,X1))
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1672,c_1534]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8096,plain,
% 3.82/1.01      ( ~ r1_waybel_0(sK6,X0_57,sK2(sK6,X0_57,X0_58))
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
% 3.82/1.01      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1690]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8849,plain,
% 3.82/1.01      ( r1_waybel_0(sK6,X0_57,sK2(sK6,X0_57,X0_58)) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57)) = iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8096]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10889,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(sK0(sK6,X0_57,k1_xboole_0),k10_yellow_6(sK6,X0_57)) = iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_10884,c_8849]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_19,plain,
% 3.82/1.01      ( r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1459,plain,
% 3.82/1.01      ( r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1460,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1459]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1464,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1460,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1465,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK6,X0))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1464]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8102,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,X0_58)
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | ~ r2_hidden(X0_58,k10_yellow_6(sK6,X0_57))
% 3.82/1.01      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1465]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8843,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,X0_58) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(X0_58,k10_yellow_6(sK6,X0_57)) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8102]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11136,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_10889,c_8843]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11271,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8851,c_11136]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11276,plain,
% 3.82/1.01      ( l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_11271,c_9616]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11277,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,X0_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_11276]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_20,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | r3_waybel_9(X0,X3,X2)
% 3.82/1.01      | ~ m2_yellow_6(X1,X0,X3)
% 3.82/1.01      | ~ l1_waybel_0(X3,X0)
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X3)
% 3.82/1.01      | ~ v4_orders_2(X3)
% 3.82/1.01      | ~ v7_waybel_0(X3)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1427,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | r3_waybel_9(X0,X3,X2)
% 3.82/1.01      | ~ m2_yellow_6(X1,X0,X3)
% 3.82/1.01      | ~ l1_waybel_0(X3,X0)
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X3)
% 3.82/1.01      | ~ v4_orders_2(X3)
% 3.82/1.01      | ~ v7_waybel_0(X3)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1428,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | r3_waybel_9(sK6,X2,X1)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1427]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1430,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | r3_waybel_9(sK6,X2,X1)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X2) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1428,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1431,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | r3_waybel_9(sK6,X2,X1)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1430]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8103,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0_57,X0_58)
% 3.82/1.01      | r3_waybel_9(sK6,X1_57,X0_58)
% 3.82/1.01      | ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.82/1.01      | ~ l1_waybel_0(X1_57,sK6)
% 3.82/1.01      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X1_57)
% 3.82/1.01      | ~ v4_orders_2(X1_57)
% 3.82/1.01      | ~ v7_waybel_0(X1_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1431]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8842,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.82/1.01      | r3_waybel_9(sK6,X1_57,X0_58) = iProver_top
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8103]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10156,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = X0_58
% 3.82/1.01      | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,X0_58)) != iProver_top
% 3.82/1.01      | r3_waybel_9(sK6,X2_57,sK0(sK6,X0_57,X0_58)) = iProver_top
% 3.82/1.01      | m2_yellow_6(X1_57,sK6,X2_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X2_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X2_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X2_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X2_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8851,c_8842]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11283,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_11277,c_10156]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_4,plain,
% 3.82/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | l1_waybel_0(X0,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_struct_0(X1) ),
% 3.82/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_667,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | l1_waybel_0(X0,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X3)
% 3.82/1.01      | X1 != X3 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_668,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | l1_waybel_0(X0,X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X1) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_667]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1943,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | l1_waybel_0(X0,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_668,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1944,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | l1_waybel_0(X0,sK6)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1943]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1946,plain,
% 3.82/1.01      ( v2_struct_0(X1)
% 3.82/1.01      | l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1944,c_39]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1947,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | l1_waybel_0(X0,sK6)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1946]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8092,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.82/1.01      | ~ l1_waybel_0(X1_57,sK6)
% 3.82/1.01      | l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | v2_struct_0(X1_57)
% 3.82/1.01      | ~ v4_orders_2(X1_57)
% 3.82/1.01      | ~ v7_waybel_0(X1_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1947]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8228,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8092]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_14,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_struct_0(X1) ),
% 3.82/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_639,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X3)
% 3.82/1.01      | X1 != X3 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_640,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_639]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1969,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | v7_waybel_0(X0)
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_640,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1970,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | v7_waybel_0(X0) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1969]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1972,plain,
% 3.82/1.01      ( v2_struct_0(X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | v7_waybel_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1970,c_39]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1973,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1972]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8091,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.82/1.01      | ~ l1_waybel_0(X1_57,sK6)
% 3.82/1.01      | v2_struct_0(X1_57)
% 3.82/1.01      | ~ v4_orders_2(X1_57)
% 3.82/1.01      | ~ v7_waybel_0(X1_57)
% 3.82/1.01      | v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1973]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8229,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8091]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_15,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_struct_0(X1) ),
% 3.82/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_611,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X3)
% 3.82/1.01      | X1 != X3 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_15]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_612,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X1) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_611]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1995,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_612,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1996,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1995]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1998,plain,
% 3.82/1.01      ( v2_struct_0(X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1996,c_39]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1999,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1998]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8090,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.82/1.01      | ~ l1_waybel_0(X1_57,sK6)
% 3.82/1.01      | v2_struct_0(X1_57)
% 3.82/1.01      | ~ v4_orders_2(X1_57)
% 3.82/1.01      | v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X1_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1999]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8230,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) = iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8090]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_16,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | ~ v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_struct_0(X1) ),
% 3.82/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_583,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | ~ v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X3)
% 3.82/1.01      | X1 != X3 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_584,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | ~ v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ l1_pre_topc(X1) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_583]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2021,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X2,X1)
% 3.82/1.01      | ~ v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_584,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2022,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | ~ v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_2021]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2024,plain,
% 3.82/1.01      ( v2_struct_0(X1)
% 3.82/1.01      | ~ v2_struct_0(X0)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2022,c_39]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2025,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | ~ v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_2024]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8089,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,X1_57)
% 3.82/1.01      | ~ l1_waybel_0(X1_57,sK6)
% 3.82/1.01      | ~ v2_struct_0(X0_57)
% 3.82/1.01      | v2_struct_0(X1_57)
% 3.82/1.01      | ~ v4_orders_2(X1_57)
% 3.82/1.01      | ~ v7_waybel_0(X1_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_2025]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8231,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8089]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13065,plain,
% 3.82/1.01      ( v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_11283,c_8228,c_8229,c_8230,c_8231,c_9616]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13066,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,X1_57,sK0(sK6,X0_57,k1_xboole_0)) = iProver_top
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_13065]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_23,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,sK4(X0),X1)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.82/1.01      | v1_compts_1(X0)
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1340,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,sK4(X0),X1)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.82/1.01      | v1_compts_1(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1341,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
% 3.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1340]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1345,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,sK4(sK6),X0)
% 3.82/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK6))
% 3.82/1.01      | v1_compts_1(sK6) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1341,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8106,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,sK4(sK6),X0_58)
% 3.82/1.01      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.82/1.01      | v1_compts_1(sK6) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1345]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8839,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,sK4(sK6),X0_58) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8106]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13071,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.82/1.01      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_13066,c_8839]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_27,plain,
% 3.82/1.01      ( v1_compts_1(X0)
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v2_struct_0(sK4(X0))
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1284,plain,
% 3.82/1.01      ( v1_compts_1(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v2_struct_0(sK4(X0))
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1285,plain,
% 3.82/1.01      ( v1_compts_1(sK6)
% 3.82/1.01      | ~ v2_struct_0(sK4(sK6))
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1284]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1287,plain,
% 3.82/1.01      ( v1_compts_1(sK6) | ~ v2_struct_0(sK4(sK6)) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1285,c_39,c_38,c_37,c_63]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1289,plain,
% 3.82/1.01      ( v1_compts_1(sK6) = iProver_top | v2_struct_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_1287]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_26,plain,
% 3.82/1.01      ( v1_compts_1(X0)
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v4_orders_2(sK4(X0))
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1298,plain,
% 3.82/1.01      ( v1_compts_1(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v4_orders_2(sK4(X0))
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1299,plain,
% 3.82/1.01      ( v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | v4_orders_2(sK4(sK6))
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1298]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1301,plain,
% 3.82/1.01      ( v4_orders_2(sK4(sK6)) | v1_compts_1(sK6) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1299,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1302,plain,
% 3.82/1.01      ( v1_compts_1(sK6) | v4_orders_2(sK4(sK6)) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1301]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1303,plain,
% 3.82/1.01      ( v1_compts_1(sK6) = iProver_top | v4_orders_2(sK4(sK6)) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_25,plain,
% 3.82/1.01      ( v1_compts_1(X0)
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v7_waybel_0(sK4(X0))
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1312,plain,
% 3.82/1.01      ( v1_compts_1(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v7_waybel_0(sK4(X0))
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1313,plain,
% 3.82/1.01      ( v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | v7_waybel_0(sK4(sK6))
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1312]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1315,plain,
% 3.82/1.01      ( v7_waybel_0(sK4(sK6)) | v1_compts_1(sK6) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1313,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1316,plain,
% 3.82/1.01      ( v1_compts_1(sK6) | v7_waybel_0(sK4(sK6)) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1315]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1317,plain,
% 3.82/1.01      ( v1_compts_1(sK6) = iProver_top | v7_waybel_0(sK4(sK6)) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_1316]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_24,plain,
% 3.82/1.01      ( l1_waybel_0(sK4(X0),X0)
% 3.82/1.01      | v1_compts_1(X0)
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1326,plain,
% 3.82/1.01      ( l1_waybel_0(sK4(X0),X0)
% 3.82/1.01      | v1_compts_1(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1327,plain,
% 3.82/1.01      ( l1_waybel_0(sK4(sK6),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1326]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1329,plain,
% 3.82/1.01      ( l1_waybel_0(sK4(sK6),sK6) | v1_compts_1(sK6) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1327,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1331,plain,
% 3.82/1.01      ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13096,plain,
% 3.82/1.01      ( v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_13071,c_1289,c_1303,c_1317,c_1331]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13097,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.82/1.01      | m1_subset_1(sK0(sK6,X0_57,k1_xboole_0),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_13096]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13102,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8851,c_13097]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9168,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
% 3.82/1.01      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.82/1.01      | v2_struct_0(sK4(sK6))
% 3.82/1.01      | v4_orders_2(X0_57)
% 3.82/1.01      | ~ v4_orders_2(sK4(sK6))
% 3.82/1.01      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8090]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9169,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_9168]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9167,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
% 3.82/1.01      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.82/1.01      | v2_struct_0(sK4(sK6))
% 3.82/1.01      | ~ v4_orders_2(sK4(sK6))
% 3.82/1.01      | v7_waybel_0(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8091]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9173,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.82/1.01      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) = iProver_top
% 3.82/1.01      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_9167]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9166,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,sK4(sK6))
% 3.82/1.01      | l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK4(sK6),sK6)
% 3.82/1.01      | v2_struct_0(sK4(sK6))
% 3.82/1.01      | ~ v4_orders_2(sK4(sK6))
% 3.82/1.01      | ~ v7_waybel_0(sK4(sK6)) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8092]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9177,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) = iProver_top
% 3.82/1.01      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.82/1.01      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_9166]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13107,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK4(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_13102,c_1289,c_1303,c_1317,c_1331,c_9169,c_9173,c_9177,
% 3.82/1.01                 c_9616]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13114,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK8(sK4(sK6))) = k1_xboole_0
% 3.82/1.01      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(sK8(sK4(sK6))) = iProver_top
% 3.82/1.01      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.82/1.01      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8828,c_13107]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2576,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | l1_waybel_0(X2,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | X1 != X0
% 3.82/1.01      | sK8(X0) != X2
% 3.82/1.01      | sK6 != sK6 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_36,c_1947]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2577,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | l1_waybel_0(sK8(X0),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_2576]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2552,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | v7_waybel_0(X2)
% 3.82/1.01      | X1 != X0
% 3.82/1.01      | sK8(X0) != X2
% 3.82/1.01      | sK6 != sK6 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_36,c_1973]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2553,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | v7_waybel_0(sK8(X0)) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_2552]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2528,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | v4_orders_2(X2)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | X1 != X0
% 3.82/1.01      | sK8(X0) != X2
% 3.82/1.01      | sK6 != sK6 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_36,c_1999]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2529,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | v4_orders_2(sK8(X0))
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_2528]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2504,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(X1,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | ~ v2_struct_0(X2)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | X1 != X0
% 3.82/1.01      | sK8(X0) != X2
% 3.82/1.01      | sK6 != sK6 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_36,c_2025]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2505,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v2_struct_0(sK8(X0))
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_2504]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_18,plain,
% 3.82/1.01      ( ~ v3_yellow_6(X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | ~ v2_pre_topc(X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 3.82/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_35,negated_conjecture,
% 3.82/1.01      ( v3_yellow_6(sK8(X0),sK6)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_765,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X2,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | ~ v2_pre_topc(X1)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X2)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X2)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | k10_yellow_6(X1,X0) != k1_xboole_0
% 3.82/1.01      | sK8(X2) != X0
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_766,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | ~ v2_pre_topc(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK8(X0))
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v4_orders_2(sK8(X0))
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v7_waybel_0(sK8(X0))
% 3.82/1.01      | ~ l1_pre_topc(sK6)
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_765]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_770,plain,
% 3.82/1.01      ( ~ v7_waybel_0(sK8(X0))
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(sK8(X0))
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK8(X0))
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_766,c_39,c_38,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_771,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK8(X0))
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v4_orders_2(sK8(X0))
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v7_waybel_0(sK8(X0))
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_770]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2759,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v4_orders_2(sK8(X0))
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v7_waybel_0(sK8(X0))
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.82/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2505,c_771]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2770,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v7_waybel_0(sK8(X0))
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.82/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2529,c_2759]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2781,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK8(X0),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.82/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2553,c_2770]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_2787,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0)) != k1_xboole_0 ),
% 3.82/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2577,c_2781]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8088,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57)
% 3.82/1.01      | k10_yellow_6(sK6,sK8(X0_57)) != k1_xboole_0 ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_2787]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9214,plain,
% 3.82/1.01      ( ~ l1_waybel_0(sK4(sK6),sK6)
% 3.82/1.01      | v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(sK4(sK6))
% 3.82/1.01      | ~ v4_orders_2(sK4(sK6))
% 3.82/1.01      | ~ v7_waybel_0(sK4(sK6))
% 3.82/1.01      | k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0 ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8088]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9215,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK8(sK4(sK6))) != k1_xboole_0
% 3.82/1.01      | l1_waybel_0(sK4(sK6),sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.82/1.01      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_9214]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8107,plain,
% 3.82/1.01      ( l1_waybel_0(sK4(sK6),sK6) | v1_compts_1(sK6) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1329]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8838,plain,
% 3.82/1.01      ( l1_waybel_0(sK4(sK6),sK6) = iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8107]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8856,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,X1_57) != iProver_top
% 3.82/1.01      | l1_waybel_0(X1_57,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) != iProver_top
% 3.82/1.01      | v2_struct_0(X1_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X1_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X1_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8089]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9196,plain,
% 3.82/1.01      ( l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(sK8(X0_57)) != iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8828,c_8856]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9278,plain,
% 3.82/1.01      ( v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(sK8(sK4(sK6))) != iProver_top
% 3.82/1.01      | v2_struct_0(sK4(sK6)) = iProver_top
% 3.82/1.01      | v4_orders_2(sK4(sK6)) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK4(sK6)) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8838,c_9196]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9509,plain,
% 3.82/1.01      ( v2_struct_0(sK8(sK4(sK6))) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) = iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_9278,c_1289,c_1303,c_1317]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9510,plain,
% 3.82/1.01      ( v1_compts_1(sK6) = iProver_top
% 3.82/1.01      | v2_struct_0(sK8(sK4(sK6))) != iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_9509]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13256,plain,
% 3.82/1.01      ( v1_compts_1(sK6) = iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_13114,c_1289,c_1303,c_1317,c_1331,c_9215,c_9510]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_28,plain,
% 3.82/1.01      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | ~ v1_compts_1(X0)
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1254,plain,
% 3.82/1.01      ( r3_waybel_9(X0,X1,sK5(X0,X1))
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | ~ v1_compts_1(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1255,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1254]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1259,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1255,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1260,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0,sK5(sK6,X0))
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1259]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8111,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57))
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1260]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8834,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,sK5(sK6,X0_57)) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8111]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_22,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1361,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | m2_yellow_6(sK3(X0,X1,X2),X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1362,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1361]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1366,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1362,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1367,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | m2_yellow_6(sK3(sK6,X0,X1),sK6,X0)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1366]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8105,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0_57,X0_58)
% 3.82/1.01      | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57)
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1367]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8840,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.82/1.01      | m2_yellow_6(sK3(sK6,X0_57,X0_58),sK6,X0_57) = iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8105]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_17,plain,
% 3.82/1.01      ( v3_yellow_6(X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | ~ v2_pre_topc(X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 3.82/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_30,negated_conjecture,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.82/1.01      | ~ v3_yellow_6(X0,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6) ),
% 3.82/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_732,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.82/1.01      | ~ l1_waybel_0(X1,X2)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | ~ v2_pre_topc(X2)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X2)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X2)
% 3.82/1.01      | X0 != X1
% 3.82/1.01      | k10_yellow_6(X2,X1) = k1_xboole_0
% 3.82/1.01      | sK6 != X2 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_733,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | ~ v2_pre_topc(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6)
% 3.82/1.01      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_732]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_737,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ m2_yellow_6(X0,sK6,sK7)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_733,c_39,c_38,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_738,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0,sK6,sK7)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | k10_yellow_6(sK6,X0) = k1_xboole_0 ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_737]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8112,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57)
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = k1_xboole_0 ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_738]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8833,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8112]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_34,negated_conjecture,
% 3.82/1.01      ( ~ v1_compts_1(sK6) | ~ v2_struct_0(sK7) ),
% 3.82/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_49,plain,
% 3.82/1.01      ( v1_compts_1(sK6) != iProver_top | v2_struct_0(sK7) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_33,negated_conjecture,
% 3.82/1.01      ( ~ v1_compts_1(sK6) | v4_orders_2(sK7) ),
% 3.82/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_50,plain,
% 3.82/1.01      ( v1_compts_1(sK6) != iProver_top | v4_orders_2(sK7) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_32,negated_conjecture,
% 3.82/1.01      ( ~ v1_compts_1(sK6) | v7_waybel_0(sK7) ),
% 3.82/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_51,plain,
% 3.82/1.01      ( v1_compts_1(sK6) != iProver_top | v7_waybel_0(sK7) = iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_31,negated_conjecture,
% 3.82/1.01      ( l1_waybel_0(sK7,sK6) | ~ v1_compts_1(sK6) ),
% 3.82/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_52,plain,
% 3.82/1.01      ( l1_waybel_0(sK7,sK6) = iProver_top | v1_compts_1(sK6) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8184,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8112]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8947,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.82/1.01      | ~ l1_waybel_0(sK7,sK6)
% 3.82/1.01      | v2_struct_0(sK7)
% 3.82/1.01      | v4_orders_2(X0_57)
% 3.82/1.01      | ~ v4_orders_2(sK7)
% 3.82/1.01      | ~ v7_waybel_0(sK7) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8090]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8948,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8947]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8952,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.82/1.01      | ~ l1_waybel_0(sK7,sK6)
% 3.82/1.01      | v2_struct_0(sK7)
% 3.82/1.01      | ~ v4_orders_2(sK7)
% 3.82/1.01      | v7_waybel_0(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(sK7) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8091]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8953,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) = iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8952]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8957,plain,
% 3.82/1.01      ( ~ m2_yellow_6(X0_57,sK6,sK7)
% 3.82/1.01      | l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | ~ l1_waybel_0(sK7,sK6)
% 3.82/1.01      | v2_struct_0(sK7)
% 3.82/1.01      | ~ v4_orders_2(sK7)
% 3.82/1.01      | ~ v7_waybel_0(sK7) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8092]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8958,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) = iProver_top
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8957]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9060,plain,
% 3.82/1.01      ( m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_8833,c_49,c_50,c_51,c_52,c_8184,c_8948,c_8953,c_8958]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_9061,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,X0_57) = k1_xboole_0
% 3.82/1.01      | m2_yellow_6(X0_57,sK6,sK7) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_9060]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10039,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8840,c_9061]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10585,plain,
% 3.82/1.01      ( v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_10039,c_49,c_50,c_51,c_52]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10586,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK3(sK6,sK7,X0_58)) = iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_10585]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10038,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v2_struct_0(sK3(sK6,X0_57,X0_58)) != iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8840,c_8856]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_10591,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_10586,c_10038]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11587,plain,
% 3.82/1.01      ( v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_10591,c_49,c_50,c_51,c_52]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11588,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK3(sK6,sK7,X0_58)) = k1_xboole_0
% 3.82/1.01      | r3_waybel_9(sK6,sK7,X0_58) != iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_11587]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11593,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_8834,c_11588]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_29,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.82/1.01      | ~ v1_compts_1(X1)
% 3.82/1.01      | ~ v2_pre_topc(X1)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1) ),
% 3.82/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1636,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,X1)
% 3.82/1.01      | m1_subset_1(sK5(X1,X0),u1_struct_0(X1))
% 3.82/1.01      | ~ v1_compts_1(X1)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(X1)
% 3.82/1.01      | sK6 != X1 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1637,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1636]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1641,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1637,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1642,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | m1_subset_1(sK5(sK6,X0),u1_struct_0(sK6))
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1641]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8099,plain,
% 3.82/1.01      ( ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | m1_subset_1(sK5(sK6,X0_57),u1_struct_0(sK6))
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1642]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8936,plain,
% 3.82/1.01      ( ~ l1_waybel_0(sK7,sK6)
% 3.82/1.01      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6))
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(sK7)
% 3.82/1.01      | ~ v4_orders_2(sK7)
% 3.82/1.01      | ~ v7_waybel_0(sK7) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8099]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8937,plain,
% 3.82/1.01      ( l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) = iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8936]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11900,plain,
% 3.82/1.01      ( v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_11593,c_49,c_50,c_51,c_52,c_8937]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_11901,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_11900]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13261,plain,
% 3.82/1.01      ( k10_yellow_6(sK6,sK3(sK6,sK7,sK5(sK6,sK7))) = k1_xboole_0 ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_13256,c_11901]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_21,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | ~ v2_pre_topc(X0)
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0) ),
% 3.82/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1394,plain,
% 3.82/1.01      ( ~ r3_waybel_9(X0,X1,X2)
% 3.82/1.01      | ~ l1_waybel_0(X1,X0)
% 3.82/1.01      | r2_hidden(X2,k10_yellow_6(X0,sK3(X0,X1,X2)))
% 3.82/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(X1)
% 3.82/1.01      | ~ v4_orders_2(X1)
% 3.82/1.01      | ~ v7_waybel_0(X1)
% 3.82/1.01      | ~ l1_pre_topc(X0)
% 3.82/1.01      | sK6 != X0 ),
% 3.82/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1395,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | v2_struct_0(sK6)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ l1_pre_topc(sK6) ),
% 3.82/1.01      inference(unflattening,[status(thm)],[c_1394]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1399,plain,
% 3.82/1.01      ( ~ v7_waybel_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0) ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_1395,c_39,c_37]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_1400,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0,X1)
% 3.82/1.01      | ~ l1_waybel_0(X0,sK6)
% 3.82/1.01      | r2_hidden(X1,k10_yellow_6(sK6,sK3(sK6,X0,X1)))
% 3.82/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0)
% 3.82/1.01      | ~ v4_orders_2(X0)
% 3.82/1.01      | ~ v7_waybel_0(X0) ),
% 3.82/1.01      inference(renaming,[status(thm)],[c_1399]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8104,plain,
% 3.82/1.01      ( ~ r3_waybel_9(sK6,X0_57,X0_58)
% 3.82/1.01      | ~ l1_waybel_0(X0_57,sK6)
% 3.82/1.01      | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58)))
% 3.82/1.01      | ~ m1_subset_1(X0_58,u1_struct_0(sK6))
% 3.82/1.01      | v2_struct_0(X0_57)
% 3.82/1.01      | ~ v4_orders_2(X0_57)
% 3.82/1.01      | ~ v7_waybel_0(X0_57) ),
% 3.82/1.01      inference(subtyping,[status(esa)],[c_1400]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8841,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,X0_57,X0_58) != iProver_top
% 3.82/1.01      | l1_waybel_0(X0_57,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(X0_58,k10_yellow_6(sK6,sK3(sK6,X0_57,X0_58))) = iProver_top
% 3.82/1.01      | m1_subset_1(X0_58,u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(X0_57) = iProver_top
% 3.82/1.01      | v4_orders_2(X0_57) != iProver_top
% 3.82/1.01      | v7_waybel_0(X0_57) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8104]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13428,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) != iProver_top
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top
% 3.82/1.01      | m1_subset_1(sK5(sK6,sK7),u1_struct_0(sK6)) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_13261,c_8841]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8939,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7))
% 3.82/1.01      | ~ l1_waybel_0(sK7,sK6)
% 3.82/1.01      | ~ v1_compts_1(sK6)
% 3.82/1.01      | v2_struct_0(sK7)
% 3.82/1.01      | ~ v4_orders_2(sK7)
% 3.82/1.01      | ~ v7_waybel_0(sK7) ),
% 3.82/1.01      inference(instantiation,[status(thm)],[c_8111]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_8940,plain,
% 3.82/1.01      ( r3_waybel_9(sK6,sK7,sK5(sK6,sK7)) = iProver_top
% 3.82/1.01      | l1_waybel_0(sK7,sK6) != iProver_top
% 3.82/1.01      | v1_compts_1(sK6) != iProver_top
% 3.82/1.01      | v2_struct_0(sK7) = iProver_top
% 3.82/1.01      | v4_orders_2(sK7) != iProver_top
% 3.82/1.01      | v7_waybel_0(sK7) != iProver_top ),
% 3.82/1.01      inference(predicate_to_equality,[status(thm)],[c_8939]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13515,plain,
% 3.82/1.01      ( r2_hidden(sK5(sK6,sK7),k1_xboole_0) = iProver_top ),
% 3.82/1.01      inference(global_propositional_subsumption,
% 3.82/1.01                [status(thm)],
% 3.82/1.01                [c_13428,c_49,c_50,c_51,c_52,c_1289,c_1303,c_1317,c_1331,
% 3.82/1.01                 c_8937,c_8940,c_9215,c_9510,c_13114]) ).
% 3.82/1.01  
% 3.82/1.01  cnf(c_13519,plain,
% 3.82/1.01      ( $false ),
% 3.82/1.01      inference(superposition,[status(thm)],[c_13515,c_8831]) ).
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/1.01  
% 3.82/1.01  ------                               Statistics
% 3.82/1.01  
% 3.82/1.01  ------ General
% 3.82/1.01  
% 3.82/1.01  abstr_ref_over_cycles:                  0
% 3.82/1.01  abstr_ref_under_cycles:                 0
% 3.82/1.01  gc_basic_clause_elim:                   0
% 3.82/1.01  forced_gc_time:                         0
% 3.82/1.01  parsing_time:                           0.009
% 3.82/1.01  unif_index_cands_time:                  0.
% 3.82/1.01  unif_index_add_time:                    0.
% 3.82/1.01  orderings_time:                         0.
% 3.82/1.01  out_proof_time:                         0.022
% 3.82/1.01  total_time:                             0.405
% 3.82/1.01  num_of_symbols:                         60
% 3.82/1.01  num_of_terms:                           8870
% 3.82/1.01  
% 3.82/1.01  ------ Preprocessing
% 3.82/1.01  
% 3.82/1.01  num_of_splits:                          0
% 3.82/1.01  num_of_split_atoms:                     0
% 3.82/1.01  num_of_reused_defs:                     0
% 3.82/1.01  num_eq_ax_congr_red:                    46
% 3.82/1.01  num_of_sem_filtered_clauses:            1
% 3.82/1.01  num_of_subtypes:                        3
% 3.82/1.01  monotx_restored_types:                  0
% 3.82/1.01  sat_num_of_epr_types:                   0
% 3.82/1.01  sat_num_of_non_cyclic_types:            0
% 3.82/1.01  sat_guarded_non_collapsed_types:        1
% 3.82/1.01  num_pure_diseq_elim:                    0
% 3.82/1.01  simp_replaced_by:                       0
% 3.82/1.01  res_preprocessed:                       191
% 3.82/1.01  prep_upred:                             0
% 3.82/1.01  prep_unflattend:                        205
% 3.82/1.01  smt_new_axioms:                         0
% 3.82/1.01  pred_elim_cands:                        11
% 3.82/1.01  pred_elim:                              5
% 3.82/1.01  pred_elim_cl:                           6
% 3.82/1.01  pred_elim_cycles:                       17
% 3.82/1.01  merged_defs:                            2
% 3.82/1.01  merged_defs_ncl:                        0
% 3.82/1.01  bin_hyper_res:                          2
% 3.82/1.01  prep_cycles:                            4
% 3.82/1.01  pred_elim_time:                         0.136
% 3.82/1.01  splitting_time:                         0.
% 3.82/1.01  sem_filter_time:                        0.
% 3.82/1.01  monotx_time:                            0.
% 3.82/1.01  subtype_inf_time:                       0.
% 3.82/1.01  
% 3.82/1.01  ------ Problem properties
% 3.82/1.01  
% 3.82/1.01  clauses:                                34
% 3.82/1.01  conjectures:                            6
% 3.82/1.01  epr:                                    10
% 3.82/1.01  horn:                                   11
% 3.82/1.01  ground:                                 9
% 3.82/1.01  unary:                                  3
% 3.82/1.01  binary:                                 9
% 3.82/1.01  lits:                                   167
% 3.82/1.01  lits_eq:                                6
% 3.82/1.01  fd_pure:                                0
% 3.82/1.01  fd_pseudo:                              0
% 3.82/1.01  fd_cond:                                0
% 3.82/1.01  fd_pseudo_cond:                         4
% 3.82/1.01  ac_symbols:                             0
% 3.82/1.01  
% 3.82/1.01  ------ Propositional Solver
% 3.82/1.01  
% 3.82/1.01  prop_solver_calls:                      29
% 3.82/1.01  prop_fast_solver_calls:                 4996
% 3.82/1.01  smt_solver_calls:                       0
% 3.82/1.01  smt_fast_solver_calls:                  0
% 3.82/1.01  prop_num_of_clauses:                    3529
% 3.82/1.01  prop_preprocess_simplified:             10754
% 3.82/1.01  prop_fo_subsumed:                       216
% 3.82/1.01  prop_solver_time:                       0.
% 3.82/1.01  smt_solver_time:                        0.
% 3.82/1.01  smt_fast_solver_time:                   0.
% 3.82/1.01  prop_fast_solver_time:                  0.
% 3.82/1.01  prop_unsat_core_time:                   0.
% 3.82/1.01  
% 3.82/1.01  ------ QBF
% 3.82/1.01  
% 3.82/1.01  qbf_q_res:                              0
% 3.82/1.01  qbf_num_tautologies:                    0
% 3.82/1.01  qbf_prep_cycles:                        0
% 3.82/1.01  
% 3.82/1.01  ------ BMC1
% 3.82/1.01  
% 3.82/1.01  bmc1_current_bound:                     -1
% 3.82/1.01  bmc1_last_solved_bound:                 -1
% 3.82/1.01  bmc1_unsat_core_size:                   -1
% 3.82/1.01  bmc1_unsat_core_parents_size:           -1
% 3.82/1.01  bmc1_merge_next_fun:                    0
% 3.82/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.82/1.01  
% 3.82/1.01  ------ Instantiation
% 3.82/1.01  
% 3.82/1.01  inst_num_of_clauses:                    802
% 3.82/1.01  inst_num_in_passive:                    99
% 3.82/1.01  inst_num_in_active:                     471
% 3.82/1.01  inst_num_in_unprocessed:                232
% 3.82/1.01  inst_num_of_loops:                      560
% 3.82/1.01  inst_num_of_learning_restarts:          0
% 3.82/1.01  inst_num_moves_active_passive:          84
% 3.82/1.01  inst_lit_activity:                      0
% 3.82/1.01  inst_lit_activity_moves:                0
% 3.82/1.01  inst_num_tautologies:                   0
% 3.82/1.01  inst_num_prop_implied:                  0
% 3.82/1.01  inst_num_existing_simplified:           0
% 3.82/1.01  inst_num_eq_res_simplified:             0
% 3.82/1.01  inst_num_child_elim:                    0
% 3.82/1.01  inst_num_of_dismatching_blockings:      113
% 3.82/1.01  inst_num_of_non_proper_insts:           525
% 3.82/1.01  inst_num_of_duplicates:                 0
% 3.82/1.01  inst_inst_num_from_inst_to_res:         0
% 3.82/1.01  inst_dismatching_checking_time:         0.
% 3.82/1.01  
% 3.82/1.01  ------ Resolution
% 3.82/1.01  
% 3.82/1.01  res_num_of_clauses:                     0
% 3.82/1.01  res_num_in_passive:                     0
% 3.82/1.01  res_num_in_active:                      0
% 3.82/1.01  res_num_of_loops:                       195
% 3.82/1.01  res_forward_subset_subsumed:            16
% 3.82/1.01  res_backward_subset_subsumed:           0
% 3.82/1.01  res_forward_subsumed:                   0
% 3.82/1.01  res_backward_subsumed:                  0
% 3.82/1.01  res_forward_subsumption_resolution:     19
% 3.82/1.01  res_backward_subsumption_resolution:    6
% 3.82/1.01  res_clause_to_clause_subsumption:       1169
% 3.82/1.01  res_orphan_elimination:                 0
% 3.82/1.01  res_tautology_del:                      26
% 3.82/1.01  res_num_eq_res_simplified:              0
% 3.82/1.01  res_num_sel_changes:                    0
% 3.82/1.01  res_moves_from_active_to_pass:          0
% 3.82/1.01  
% 3.82/1.01  ------ Superposition
% 3.82/1.01  
% 3.82/1.01  sup_time_total:                         0.
% 3.82/1.01  sup_time_generating:                    0.
% 3.82/1.01  sup_time_sim_full:                      0.
% 3.82/1.01  sup_time_sim_immed:                     0.
% 3.82/1.01  
% 3.82/1.01  sup_num_of_clauses:                     103
% 3.82/1.01  sup_num_in_active:                      63
% 3.82/1.01  sup_num_in_passive:                     40
% 3.82/1.01  sup_num_of_loops:                       111
% 3.82/1.01  sup_fw_superposition:                   53
% 3.82/1.01  sup_bw_superposition:                   130
% 3.82/1.01  sup_immediate_simplified:               59
% 3.82/1.01  sup_given_eliminated:                   2
% 3.82/1.01  comparisons_done:                       0
% 3.82/1.01  comparisons_avoided:                    3
% 3.82/1.01  
% 3.82/1.01  ------ Simplifications
% 3.82/1.01  
% 3.82/1.01  
% 3.82/1.01  sim_fw_subset_subsumed:                 20
% 3.82/1.01  sim_bw_subset_subsumed:                 17
% 3.82/1.01  sim_fw_subsumed:                        30
% 3.82/1.01  sim_bw_subsumed:                        33
% 3.82/1.01  sim_fw_subsumption_res:                 0
% 3.82/1.01  sim_bw_subsumption_res:                 0
% 3.82/1.01  sim_tautology_del:                      12
% 3.82/1.01  sim_eq_tautology_del:                   9
% 3.82/1.01  sim_eq_res_simp:                        0
% 3.82/1.01  sim_fw_demodulated:                     4
% 3.82/1.01  sim_bw_demodulated:                     1
% 3.82/1.01  sim_light_normalised:                   19
% 3.82/1.01  sim_joinable_taut:                      0
% 3.82/1.01  sim_joinable_simp:                      0
% 3.82/1.01  sim_ac_normalised:                      0
% 3.82/1.01  sim_smt_subsumption:                    0
% 3.82/1.01  
%------------------------------------------------------------------------------
