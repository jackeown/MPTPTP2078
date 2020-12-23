%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:26 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  345 (2697 expanded)
%              Number of clauses        :  229 ( 781 expanded)
%              Number of leaves         :   28 ( 633 expanded)
%              Depth                    :   45
%              Number of atoms          : 2758 (28269 expanded)
%              Number of equality atoms : 1116 (2683 expanded)
%              Maximal formula depth    :   19 (   9 average)
%              Maximal clause size      :   34 (   7 average)
%              Maximal term depth       :    4 (   1 average)

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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

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
    inference(nnf_transformation,[],[f43])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f70,plain,(
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
    inference(rectify,[],[f69])).

fof(f73,plain,(
    ! [X0,X3] :
      ( ? [X4] :
          ( v3_yellow_6(X4,X0)
          & m2_yellow_6(X4,X0,X3) )
     => ( v3_yellow_6(sK11(X3),X0)
        & m2_yellow_6(sK11(X3),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
            | ~ m2_yellow_6(X2,X0,sK10) )
        & l1_waybel_0(sK10,X0)
        & v7_waybel_0(sK10)
        & v4_orders_2(sK10)
        & ~ v2_struct_0(sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
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
                ( ~ v3_yellow_6(X2,sK9)
                | ~ m2_yellow_6(X2,sK9,X1) )
            & l1_waybel_0(X1,sK9)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        | ~ v1_compts_1(sK9) )
      & ( ! [X3] :
            ( ? [X4] :
                ( v3_yellow_6(X4,sK9)
                & m2_yellow_6(X4,sK9,X3) )
            | ~ l1_waybel_0(X3,sK9)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
        | v1_compts_1(sK9) )
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ( ( ! [X2] :
            ( ~ v3_yellow_6(X2,sK9)
            | ~ m2_yellow_6(X2,sK9,sK10) )
        & l1_waybel_0(sK10,sK9)
        & v7_waybel_0(sK10)
        & v4_orders_2(sK10)
        & ~ v2_struct_0(sK10) )
      | ~ v1_compts_1(sK9) )
    & ( ! [X3] :
          ( ( v3_yellow_6(sK11(X3),sK9)
            & m2_yellow_6(sK11(X3),sK9,X3) )
          | ~ l1_waybel_0(X3,sK9)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | v1_compts_1(sK9) )
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f70,f73,f72,f71])).

fof(f119,plain,(
    ! [X3] :
      ( m2_yellow_6(sK11(X3),sK9,X3)
      | ~ l1_waybel_0(X3,sK9)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK9) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f11,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f32])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_waybel_0(X0,X1,X3)
          & m1_connsp_2(X3,X0,X2) )
     => ( ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
        & m1_connsp_2(sK3(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ( ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
                    & m1_connsp_2(sK3(X0,X1,X2),X0,X2) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | m1_connsp_2(sK3(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f49,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X6))
        & m1_connsp_2(sK2(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,X3) )
     => ( ~ r1_waybel_0(X0,X1,sK1(X0,X1,X2))
        & m1_connsp_2(sK1(X0,X1,X2),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f49,f48,f47])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f127,plain,(
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
    inference(equality_resolution,[],[f81])).

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

fof(f87,plain,(
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

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f126,plain,(
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
    inference(equality_resolution,[],[f82])).

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
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f34])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f9,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f28])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

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
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f66,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK8(X0,X3))
        & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
            ( ~ r3_waybel_9(X0,sK7(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0),k6_yellow_6(X0))
        & l1_waybel_0(sK7(X0),X0)
        & v7_waybel_0(sK7(X0))
        & v4_orders_2(sK7(X0))
        & ~ v2_struct_0(sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK7(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r2_hidden(sK7(X0),k6_yellow_6(X0))
            & l1_waybel_0(sK7(X0),X0)
            & v7_waybel_0(sK7(X0))
            & v4_orders_2(sK7(X0))
            & ~ v2_struct_0(sK7(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK8(X0,X3))
                & m1_subset_1(sK8(X0,X3),u1_struct_0(X0)) )
              | ~ r2_hidden(X3,k6_yellow_6(X0))
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f64,f66,f65])).

fof(f115,plain,(
    ! [X2,X0] :
      ( v1_compts_1(X0)
      | ~ r3_waybel_9(X0,sK7(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f113,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | l1_waybel_0(sK7(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f112,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v7_waybel_0(sK7(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f111,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | v4_orders_2(sK7(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f110,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_struct_0(sK7(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f116,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f117,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f118,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f120,plain,(
    ! [X3] :
      ( v3_yellow_6(sK11(X3),sK9)
      | ~ l1_waybel_0(X3,sK9)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | v1_compts_1(sK9) ) ),
    inference(cnf_transformation,[],[f74])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f30])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f51])).

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

fof(f91,plain,(
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

fof(f90,plain,(
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

fof(f89,plain,(
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

fof(f88,plain,(
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
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f38])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f61,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X3,sK6(X0,X3))
        & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
            ( ~ r3_waybel_9(X0,sK5(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_waybel_0(sK5(X0),X0)
        & v7_waybel_0(sK5(X0))
        & v4_orders_2(sK5(X0))
        & ~ v2_struct_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ r3_waybel_9(X0,sK5(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(sK5(X0),X0)
            & v7_waybel_0(sK5(X0))
            & v4_orders_2(sK5(X0))
            & ~ v2_struct_0(sK5(X0)) ) )
        & ( ! [X3] :
              ( ( r3_waybel_9(X0,X3,sK6(X0,X3))
                & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) )
              | ~ l1_waybel_0(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f59,f61,f60])).

fof(f102,plain,(
    ! [X0,X3] :
      ( r3_waybel_9(X0,X3,sK6(X0,X3))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f36])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f56])).

fof(f99,plain,(
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

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f125,plain,(
    ! [X2] :
      ( ~ v3_yellow_6(X2,sK9)
      | ~ m2_yellow_6(X2,sK9,sK10)
      | ~ v1_compts_1(sK9) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f121,plain,
    ( ~ v2_struct_0(sK10)
    | ~ v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f122,plain,
    ( v4_orders_2(sK10)
    | ~ v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f123,plain,
    ( v7_waybel_0(sK10)
    | ~ v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f124,plain,
    ( l1_waybel_0(sK10,sK9)
    | ~ v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f74])).

fof(f101,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK6(X0,X3),u1_struct_0(X0))
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,(
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

cnf(c_47,negated_conjecture,
    ( m2_yellow_6(sK11(X0),sK9,X0)
    | ~ l1_waybel_0(X0,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_465,negated_conjecture,
    ( m2_yellow_6(sK11(X0_62),sK9,X0_62)
    | ~ l1_waybel_0(X0_62,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62) ),
    inference(subtyping,[status(esa)],[c_47])).

cnf(c_1492,plain,
    ( m2_yellow_6(sK11(X0_62),sK9,X0_62) = iProver_top
    | l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v7_waybel_0(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_21,plain,
    ( r3_waybel_9(X0,X1,X2)
    | m1_connsp_2(sK3(X0,X1,X2),X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_491,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62)
    | m1_connsp_2(sK3(X0_62,X1_62,X2_62),X0_62,X2_62)
    | ~ l1_waybel_0(X1_62,X0_62)
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1466,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
    | m1_connsp_2(sK3(X0_62,X1_62,X2_62),X0_62,X2_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_512,plain,
    ( r1_tarski(k1_xboole_0,X0_62) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1445,plain,
    ( r1_tarski(k1_xboole_0,X0_62) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

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
    inference(cnf_transformation,[],[f127])).

cnf(c_502,plain,
    ( m1_connsp_2(sK2(X0_62,X1_62,X2_62),X0_62,X2_62)
    | ~ l1_waybel_0(X1_62,X0_62)
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62))
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62)))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X1_62)
    | ~ v7_waybel_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1455,plain,
    ( m1_connsp_2(sK2(X0_62,X1_62,X2_62),X0_62,X2_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_12,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_500,plain,
    ( ~ l1_waybel_0(X0_62,X1_62)
    | m1_subset_1(k10_yellow_6(X1_62,X0_62),k1_zfmisc_1(u1_struct_0(X1_62)))
    | ~ v2_pre_topc(X1_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62)
    | ~ l1_pre_topc(X1_62) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1457,plain,
    ( l1_waybel_0(X0_62,X1_62) != iProver_top
    | m1_subset_1(k10_yellow_6(X1_62,X0_62),k1_zfmisc_1(u1_struct_0(X1_62))) = iProver_top
    | v2_pre_topc(X1_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v7_waybel_0(X0_62) != iProver_top
    | l1_pre_topc(X1_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_2053,plain,
    ( m1_connsp_2(sK2(X0_62,X1_62,X2_62),X0_62,X2_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1455,c_1457])).

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
    inference(cnf_transformation,[],[f84])).

cnf(c_505,plain,
    ( ~ m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,X2_62))
    | r1_waybel_0(X0_62,X1_62,X0_64)
    | ~ l1_waybel_0(X1_62,X0_62)
    | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62)
    | ~ m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62)))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X1_62)
    | ~ v7_waybel_0(X1_62)
    | ~ l1_pre_topc(X0_62)
    | k10_yellow_6(X0_62,X1_62) = X2_62 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1452,plain,
    ( k10_yellow_6(X0_62,X1_62) = X2_62
    | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,X2_62)) != iProver_top
    | r1_waybel_0(X0_62,X1_62,X0_64) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
    | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_6545,plain,
    ( k10_yellow_6(X0_62,X1_62) = X2_62
    | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
    | l1_waybel_0(X3_62,X0_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
    | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,X2_62),u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X3_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X3_62) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X3_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_2053,c_1452])).

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
    inference(cnf_transformation,[],[f83])).

cnf(c_504,plain,
    ( ~ l1_waybel_0(X0_62,X1_62)
    | ~ m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X1_62)))
    | m1_subset_1(sK0(X1_62,X0_62,X2_62),u1_struct_0(X1_62))
    | ~ v2_pre_topc(X1_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62)
    | ~ l1_pre_topc(X1_62)
    | k10_yellow_6(X1_62,X0_62) = X2_62 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_576,plain,
    ( k10_yellow_6(X0_62,X1_62) = X2_62
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,X2_62),u1_struct_0(X0_62)) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_9911,plain,
    ( m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X3_62,X0_62) != iProver_top
    | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
    | k10_yellow_6(X0_62,X1_62) = X2_62
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X3_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X3_62) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X3_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6545,c_576])).

cnf(c_9912,plain,
    ( k10_yellow_6(X0_62,X1_62) = X2_62
    | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X3_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
    | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X3_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X3_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X3_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_9911])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_509,plain,
    ( ~ r2_hidden(X0_62,X1_62)
    | ~ r1_tarski(X1_62,X0_62) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1448,plain,
    ( r2_hidden(X0_62,X1_62) != iProver_top
    | r1_tarski(X1_62,X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_9935,plain,
    ( k10_yellow_6(X0_62,X1_62) = X2_62
    | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X3_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
    | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | r1_tarski(X2_62,sK0(X0_62,X1_62,X2_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X3_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X3_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X3_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_9912,c_1448])).

cnf(c_10382,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X2_62)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_9935])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_511,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_63)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2487,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_2489,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2487])).

cnf(c_10491,plain,
    ( r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X2_62)) = iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10382,c_2489])).

cnf(c_10492,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X2_62)) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_10491])).

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
    inference(cnf_transformation,[],[f126])).

cnf(c_503,plain,
    ( ~ r1_waybel_0(X0_62,X1_62,sK2(X0_62,X1_62,X2_62))
    | ~ l1_waybel_0(X1_62,X0_62)
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62))
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62)))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X1_62)
    | ~ v7_waybel_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1454,plain,
    ( r1_waybel_0(X0_62,X1_62,sK2(X0_62,X1_62,X2_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_2097,plain,
    ( r1_waybel_0(X0_62,X1_62,sK2(X0_62,X1_62,X2_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1454,c_1457])).

cnf(c_10511,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X1_62)) = iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_10492,c_2097])).

cnf(c_2488,plain,
    ( ~ l1_waybel_0(X0_62,X1_62)
    | m1_subset_1(sK0(X1_62,X0_62,k1_xboole_0),u1_struct_0(X1_62))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1_62)))
    | ~ v2_pre_topc(X1_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62)
    | ~ l1_pre_topc(X1_62)
    | k10_yellow_6(X1_62,X0_62) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_2493,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2488])).

cnf(c_10516,plain,
    ( r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X1_62)) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10511,c_2489,c_2493])).

cnf(c_10517,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X1_62)) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_10516])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f98])).

cnf(c_489,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62)
    | ~ l1_waybel_0(X1_62,X0_62)
    | ~ r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62))
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X1_62)
    | ~ v7_waybel_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1468,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_510,plain,
    ( ~ r2_hidden(X0_62,X1_62)
    | m1_subset_1(X0_62,X0_63)
    | ~ m1_subset_1(X1_62,k1_zfmisc_1(X0_63)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1447,plain,
    ( r2_hidden(X0_62,X1_62) != iProver_top
    | m1_subset_1(X0_62,X0_63) = iProver_top
    | m1_subset_1(X1_62,k1_zfmisc_1(X0_63)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_4006,plain,
    ( l1_waybel_0(X0_62,X1_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X1_62,X0_62)) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X1_62)) = iProver_top
    | v2_pre_topc(X1_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v7_waybel_0(X0_62) != iProver_top
    | l1_pre_topc(X1_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_1457,c_1447])).

cnf(c_6001,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1468,c_4006])).

cnf(c_10531,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r3_waybel_9(X0_62,X1_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_10517,c_6001])).

cnf(c_22,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_waybel_0(X0,X1,X3)
    | ~ m1_connsp_2(X3,X0,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_490,plain,
    ( ~ r3_waybel_9(X0_62,X1_62,X2_62)
    | r2_waybel_0(X0_62,X1_62,X0_64)
    | ~ m1_connsp_2(X0_64,X0_62,X2_62)
    | ~ l1_waybel_0(X1_62,X0_62)
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1467,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
    | m1_connsp_2(X0_64,X0_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_10783,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
    | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,k1_xboole_0)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_10531,c_1467])).

cnf(c_13476,plain,
    ( l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,k1_xboole_0)) != iProver_top
    | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
    | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10783,c_2489,c_2493])).

cnf(c_13477,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
    | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,k1_xboole_0)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_13476])).

cnf(c_13492,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_1466,c_13477])).

cnf(c_13679,plain,
    ( l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13492,c_2489,c_2493])).

cnf(c_13680,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_13679])).

cnf(c_17,plain,
    ( ~ r2_waybel_0(X0,X1,X2)
    | r2_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X1,X0,X3)
    | ~ l1_waybel_0(X3,X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_495,plain,
    ( ~ r2_waybel_0(X0_62,X1_62,X0_64)
    | r2_waybel_0(X0_62,X2_62,X0_64)
    | ~ m2_yellow_6(X1_62,X0_62,X2_62)
    | ~ l1_waybel_0(X2_62,X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X2_62)
    | ~ v4_orders_2(X2_62)
    | ~ v7_waybel_0(X2_62)
    | ~ l1_struct_0(X0_62) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1462,plain,
    ( r2_waybel_0(X0_62,X1_62,X0_64) != iProver_top
    | r2_waybel_0(X0_62,X2_62,X0_64) = iProver_top
    | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_struct_0(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_13695,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | r2_waybel_0(X0_62,X3_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | m2_yellow_6(X1_62,X0_62,X3_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X3_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X3_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X3_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X3_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top
    | l1_struct_0(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_13680,c_1462])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_508,plain,
    ( ~ l1_pre_topc(X0_62)
    | l1_struct_0(X0_62) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_566,plain,
    ( l1_pre_topc(X0_62) != iProver_top
    | l1_struct_0(X0_62) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_19230,plain,
    ( l1_pre_topc(X0_62) != iProver_top
    | v7_waybel_0(X3_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v4_orders_2(X3_62) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v2_struct_0(X3_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | l1_waybel_0(X3_62,X0_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m2_yellow_6(X1_62,X0_62,X3_62) != iProver_top
    | r2_waybel_0(X0_62,X3_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | k10_yellow_6(X0_62,X1_62) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13695,c_566])).

cnf(c_19231,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | r2_waybel_0(X0_62,X3_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
    | m2_yellow_6(X1_62,X0_62,X3_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X3_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X3_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X3_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X3_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_19230])).

cnf(c_20,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_492,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62)
    | ~ r2_waybel_0(X0_62,X1_62,sK3(X0_62,X1_62,X2_62))
    | ~ l1_waybel_0(X1_62,X0_62)
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1465,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
    | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X1_62,X2_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_19254,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_19231,c_1465])).

cnf(c_20191,plain,
    ( l1_waybel_0(X2_62,X0_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19254,c_2489,c_2493])).

cnf(c_20192,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
    | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(X2_62,X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_20191])).

cnf(c_33,plain,
    ( ~ r3_waybel_9(X0,sK7(X0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_479,plain,
    ( ~ r3_waybel_9(X0_62,sK7(X0_62),X1_62)
    | ~ m1_subset_1(X1_62,u1_struct_0(X0_62))
    | v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1478,plain,
    ( r3_waybel_9(X0_62,sK7(X0_62),X1_62) != iProver_top
    | m1_subset_1(X1_62,u1_struct_0(X0_62)) != iProver_top
    | v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_20211,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | m2_yellow_6(X1_62,X0_62,sK7(X0_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(sK7(X0_62),X0_62) != iProver_top
    | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
    | v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(sK7(X0_62)) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(sK7(X0_62)) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(sK7(X0_62)) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_20192,c_1478])).

cnf(c_35,plain,
    ( l1_waybel_0(sK7(X0),X0)
    | v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_477,plain,
    ( l1_waybel_0(sK7(X0_62),X0_62)
    | v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_613,plain,
    ( l1_waybel_0(sK7(X0_62),X0_62) = iProver_top
    | v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_36,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v7_waybel_0(sK7(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_476,plain,
    ( v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v7_waybel_0(sK7(X0_62))
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_614,plain,
    ( v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v7_waybel_0(sK7(X0_62)) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_37,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v4_orders_2(sK7(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_475,plain,
    ( v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v4_orders_2(sK7(X0_62))
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_615,plain,
    ( v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v4_orders_2(sK7(X0_62)) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_38,plain,
    ( v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v2_struct_0(sK7(X0))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_474,plain,
    ( v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | ~ v2_struct_0(sK7(X0_62))
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_616,plain,
    ( v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK7(X0_62)) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_20585,plain,
    ( v7_waybel_0(X1_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v1_compts_1(X0_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m2_yellow_6(X1_62,X0_62,sK7(X0_62)) != iProver_top
    | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | v4_orders_2(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20211,c_613,c_614,c_615,c_616,c_2489,c_2493])).

cnf(c_20586,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | m2_yellow_6(X1_62,X0_62,sK7(X0_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_20585])).

cnf(c_20601,plain,
    ( k10_yellow_6(sK9,sK11(sK7(sK9))) = k1_xboole_0
    | l1_waybel_0(sK11(sK7(sK9)),sK9) != iProver_top
    | l1_waybel_0(sK7(sK9),sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK11(sK7(sK9))) = iProver_top
    | v2_struct_0(sK7(sK9)) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK11(sK7(sK9))) != iProver_top
    | v4_orders_2(sK7(sK9)) != iProver_top
    | v7_waybel_0(sK11(sK7(sK9))) != iProver_top
    | v7_waybel_0(sK7(sK9)) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_20586])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_51,plain,
    ( v2_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_52,plain,
    ( v2_pre_topc(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_53,plain,
    ( l1_pre_topc(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_73,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK7(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_75,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK7(sK9)) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_76,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v4_orders_2(sK7(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_78,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK7(sK9)) = iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_79,plain,
    ( v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v7_waybel_0(sK7(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_81,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v7_waybel_0(sK7(sK9)) = iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_82,plain,
    ( l1_waybel_0(sK7(X0),X0) = iProver_top
    | v1_compts_1(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_84,plain,
    ( l1_waybel_0(sK7(sK9),sK9) = iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_165,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_167,plain,
    ( l1_pre_topc(sK9) != iProver_top
    | l1_struct_0(sK9) = iProver_top ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_46,negated_conjecture,
    ( v3_yellow_6(sK11(X0),sK9)
    | ~ l1_waybel_0(X0,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_466,negated_conjecture,
    ( v3_yellow_6(sK11(X0_62),sK9)
    | ~ l1_waybel_0(X0_62,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62) ),
    inference(subtyping,[status(esa)],[c_46])).

cnf(c_2672,plain,
    ( v3_yellow_6(sK11(sK7(X0_62)),sK9)
    | ~ l1_waybel_0(sK7(X0_62),sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(sK7(X0_62))
    | ~ v4_orders_2(sK7(X0_62))
    | ~ v7_waybel_0(sK7(X0_62)) ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_2693,plain,
    ( v3_yellow_6(sK11(sK7(X0_62)),sK9) = iProver_top
    | l1_waybel_0(sK7(X0_62),sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(sK7(X0_62)) = iProver_top
    | v4_orders_2(sK7(X0_62)) != iProver_top
    | v7_waybel_0(sK7(X0_62)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2672])).

cnf(c_2695,plain,
    ( v3_yellow_6(sK11(sK7(sK9)),sK9) = iProver_top
    | l1_waybel_0(sK7(sK9),sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(sK7(sK9)) = iProver_top
    | v4_orders_2(sK7(sK9)) != iProver_top
    | v7_waybel_0(sK7(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2693])).

cnf(c_2671,plain,
    ( m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62))
    | ~ l1_waybel_0(sK7(X0_62),sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(sK7(X0_62))
    | ~ v4_orders_2(sK7(X0_62))
    | ~ v7_waybel_0(sK7(X0_62)) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_2697,plain,
    ( m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62)) = iProver_top
    | l1_waybel_0(sK7(X0_62),sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(sK7(X0_62)) = iProver_top
    | v4_orders_2(sK7(X0_62)) != iProver_top
    | v7_waybel_0(sK7(X0_62)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2671])).

cnf(c_2699,plain,
    ( m2_yellow_6(sK11(sK7(sK9)),sK9,sK7(sK9)) = iProver_top
    | l1_waybel_0(sK7(sK9),sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(sK7(sK9)) = iProver_top
    | v4_orders_2(sK7(sK9)) != iProver_top
    | v7_waybel_0(sK7(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2697])).

cnf(c_19,plain,
    ( ~ v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_493,plain,
    ( ~ v3_yellow_6(X0_62,X1_62)
    | ~ l1_waybel_0(X0_62,X1_62)
    | ~ v2_pre_topc(X1_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62)
    | ~ l1_pre_topc(X1_62)
    | k10_yellow_6(X1_62,X0_62) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2954,plain,
    ( ~ v3_yellow_6(sK11(sK7(X0_62)),sK9)
    | ~ l1_waybel_0(sK11(sK7(X0_62)),sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK11(sK7(X0_62)))
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK11(sK7(X0_62)))
    | ~ v7_waybel_0(sK11(sK7(X0_62)))
    | ~ l1_pre_topc(sK9)
    | k10_yellow_6(sK9,sK11(sK7(X0_62))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_2960,plain,
    ( k10_yellow_6(sK9,sK11(sK7(X0_62))) != k1_xboole_0
    | v3_yellow_6(sK11(sK7(X0_62)),sK9) != iProver_top
    | l1_waybel_0(sK11(sK7(X0_62)),sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK11(sK7(X0_62))) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK11(sK7(X0_62))) != iProver_top
    | v7_waybel_0(sK11(sK7(X0_62))) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2954])).

cnf(c_2962,plain,
    ( k10_yellow_6(sK9,sK11(sK7(sK9))) != k1_xboole_0
    | v3_yellow_6(sK11(sK7(sK9)),sK9) != iProver_top
    | l1_waybel_0(sK11(sK7(sK9)),sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK11(sK7(sK9))) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK11(sK7(sK9))) != iProver_top
    | v7_waybel_0(sK11(sK7(sK9))) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2960])).

cnf(c_13,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_499,plain,
    ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
    | ~ l1_waybel_0(X2_62,X1_62)
    | l1_waybel_0(X0_62,X1_62)
    | v2_struct_0(X1_62)
    | v2_struct_0(X2_62)
    | ~ v4_orders_2(X2_62)
    | ~ v7_waybel_0(X2_62)
    | ~ l1_struct_0(X1_62) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2999,plain,
    ( ~ m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62))
    | l1_waybel_0(sK11(sK7(X0_62)),sK9)
    | ~ l1_waybel_0(sK7(X0_62),sK9)
    | v2_struct_0(sK7(X0_62))
    | v2_struct_0(sK9)
    | ~ v4_orders_2(sK7(X0_62))
    | ~ v7_waybel_0(sK7(X0_62))
    | ~ l1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_3010,plain,
    ( m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62)) != iProver_top
    | l1_waybel_0(sK11(sK7(X0_62)),sK9) = iProver_top
    | l1_waybel_0(sK7(X0_62),sK9) != iProver_top
    | v2_struct_0(sK7(X0_62)) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK7(X0_62)) != iProver_top
    | v7_waybel_0(sK7(X0_62)) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2999])).

cnf(c_3012,plain,
    ( m2_yellow_6(sK11(sK7(sK9)),sK9,sK7(sK9)) != iProver_top
    | l1_waybel_0(sK11(sK7(sK9)),sK9) = iProver_top
    | l1_waybel_0(sK7(sK9),sK9) != iProver_top
    | v2_struct_0(sK7(sK9)) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK7(sK9)) != iProver_top
    | v7_waybel_0(sK7(sK9)) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_1480,plain,
    ( l1_waybel_0(sK7(X0_62),X0_62) = iProver_top
    | v1_compts_1(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_14,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_498,plain,
    ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
    | ~ l1_waybel_0(X2_62,X1_62)
    | v2_struct_0(X1_62)
    | v2_struct_0(X2_62)
    | ~ v4_orders_2(X2_62)
    | ~ v7_waybel_0(X2_62)
    | v7_waybel_0(X0_62)
    | ~ l1_struct_0(X1_62) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1459,plain,
    ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X2_62,X1_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | v7_waybel_0(X0_62) = iProver_top
    | l1_struct_0(X1_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_3518,plain,
    ( l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v7_waybel_0(X0_62) != iProver_top
    | v7_waybel_0(sK11(X0_62)) = iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_1459])).

cnf(c_3523,plain,
    ( v7_waybel_0(sK11(X0_62)) = iProver_top
    | v7_waybel_0(X0_62) != iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3518,c_51,c_53,c_167])).

cnf(c_3524,plain,
    ( l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v7_waybel_0(X0_62) != iProver_top
    | v7_waybel_0(sK11(X0_62)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3523])).

cnf(c_3536,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK7(sK9)) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK7(sK9)) != iProver_top
    | v7_waybel_0(sK11(sK7(sK9))) = iProver_top
    | v7_waybel_0(sK7(sK9)) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_3524])).

cnf(c_3689,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v7_waybel_0(sK11(sK7(sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3536,c_51,c_52,c_53,c_75,c_78,c_81])).

cnf(c_15,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_497,plain,
    ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
    | ~ l1_waybel_0(X2_62,X1_62)
    | v2_struct_0(X1_62)
    | v2_struct_0(X2_62)
    | ~ v4_orders_2(X2_62)
    | v4_orders_2(X0_62)
    | ~ v7_waybel_0(X2_62)
    | ~ l1_struct_0(X1_62) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_4218,plain,
    ( ~ l1_waybel_0(X0_62,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0_62)
    | v2_struct_0(sK9)
    | ~ v4_orders_2(X0_62)
    | v4_orders_2(sK11(X0_62))
    | ~ v7_waybel_0(X0_62)
    | ~ l1_struct_0(sK9) ),
    inference(resolution,[status(thm)],[c_497,c_465])).

cnf(c_1460,plain,
    ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X2_62,X1_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v4_orders_2(X0_62) = iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_struct_0(X1_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_3896,plain,
    ( l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v4_orders_2(sK11(X0_62)) = iProver_top
    | v7_waybel_0(X0_62) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_1460])).

cnf(c_4094,plain,
    ( v7_waybel_0(X0_62) != iProver_top
    | v4_orders_2(sK11(X0_62)) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3896,c_51,c_53,c_167])).

cnf(c_4095,plain,
    ( l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v4_orders_2(sK11(X0_62)) = iProver_top
    | v7_waybel_0(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_4094])).

cnf(c_4096,plain,
    ( ~ l1_waybel_0(X0_62,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0_62)
    | ~ v4_orders_2(X0_62)
    | v4_orders_2(sK11(X0_62))
    | ~ v7_waybel_0(X0_62) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4095])).

cnf(c_4221,plain,
    ( ~ v7_waybel_0(X0_62)
    | v4_orders_2(sK11(X0_62))
    | ~ v4_orders_2(X0_62)
    | ~ l1_waybel_0(X0_62,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0_62) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4218,c_4096])).

cnf(c_4222,plain,
    ( ~ l1_waybel_0(X0_62,sK9)
    | v1_compts_1(sK9)
    | v2_struct_0(X0_62)
    | ~ v4_orders_2(X0_62)
    | v4_orders_2(sK11(X0_62))
    | ~ v7_waybel_0(X0_62) ),
    inference(renaming,[status(thm)],[c_4221])).

cnf(c_4253,plain,
    ( v1_compts_1(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK7(sK9))
    | v2_struct_0(sK9)
    | v4_orders_2(sK11(sK7(sK9)))
    | ~ v4_orders_2(sK7(sK9))
    | ~ v7_waybel_0(sK7(sK9))
    | ~ l1_pre_topc(sK9) ),
    inference(resolution,[status(thm)],[c_4222,c_477])).

cnf(c_74,plain,
    ( v1_compts_1(sK9)
    | ~ v2_pre_topc(sK9)
    | ~ v2_struct_0(sK7(sK9))
    | v2_struct_0(sK9)
    | ~ l1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_77,plain,
    ( v1_compts_1(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | v4_orders_2(sK7(sK9))
    | ~ l1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_80,plain,
    ( v1_compts_1(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK9)
    | v7_waybel_0(sK7(sK9))
    | ~ l1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_4107,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK7(sK9)) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK11(sK7(sK9))) = iProver_top
    | v4_orders_2(sK7(sK9)) != iProver_top
    | v7_waybel_0(sK7(sK9)) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_4095])).

cnf(c_4141,plain,
    ( v1_compts_1(sK9)
    | ~ v2_pre_topc(sK9)
    | v2_struct_0(sK7(sK9))
    | v2_struct_0(sK9)
    | v4_orders_2(sK11(sK7(sK9)))
    | ~ v4_orders_2(sK7(sK9))
    | ~ v7_waybel_0(sK7(sK9))
    | ~ l1_pre_topc(sK9) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4107])).

cnf(c_4561,plain,
    ( v4_orders_2(sK11(sK7(sK9)))
    | v1_compts_1(sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4253,c_50,c_49,c_48,c_74,c_77,c_80,c_4141])).

cnf(c_4562,plain,
    ( v1_compts_1(sK9)
    | v4_orders_2(sK11(sK7(sK9))) ),
    inference(renaming,[status(thm)],[c_4561])).

cnf(c_4563,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v4_orders_2(sK11(sK7(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4562])).

cnf(c_16,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_496,plain,
    ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
    | ~ l1_waybel_0(X2_62,X1_62)
    | ~ v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | v2_struct_0(X2_62)
    | ~ v4_orders_2(X2_62)
    | ~ v7_waybel_0(X2_62)
    | ~ l1_struct_0(X1_62) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1461,plain,
    ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X2_62,X1_62) != iProver_top
    | v2_struct_0(X0_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_struct_0(X1_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_3993,plain,
    ( l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK11(X0_62)) != iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v7_waybel_0(X0_62) != iProver_top
    | l1_struct_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_1461])).

cnf(c_4482,plain,
    ( v7_waybel_0(X0_62) != iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK11(X0_62)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3993,c_51,c_53,c_167])).

cnf(c_4483,plain,
    ( l1_waybel_0(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK11(X0_62)) != iProver_top
    | v4_orders_2(X0_62) != iProver_top
    | v7_waybel_0(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_4482])).

cnf(c_4495,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK11(sK7(sK9))) != iProver_top
    | v2_struct_0(sK7(sK9)) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK7(sK9)) != iProver_top
    | v7_waybel_0(sK7(sK9)) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1480,c_4483])).

cnf(c_4711,plain,
    ( v2_struct_0(sK11(sK7(sK9))) != iProver_top
    | v1_compts_1(sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4495,c_51,c_52,c_53,c_75,c_78,c_81])).

cnf(c_4712,plain,
    ( v1_compts_1(sK9) = iProver_top
    | v2_struct_0(sK11(sK7(sK9))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4711])).

cnf(c_20646,plain,
    ( v1_compts_1(sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20601,c_51,c_52,c_53,c_75,c_78,c_81,c_84,c_167,c_2695,c_2699,c_2962,c_3012,c_3689,c_4563,c_4712])).

cnf(c_31,plain,
    ( r3_waybel_9(X0,X1,sK6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ v1_compts_1(X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_481,plain,
    ( r3_waybel_9(X0_62,X1_62,sK6(X0_62,X1_62))
    | ~ l1_waybel_0(X1_62,X0_62)
    | ~ v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X1_62)
    | ~ v7_waybel_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1476,plain,
    ( r3_waybel_9(X0_62,X1_62,sK6(X0_62,X1_62)) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | v1_compts_1(X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f99])).

cnf(c_487,plain,
    ( ~ r3_waybel_9(X0_62,X1_62,X2_62)
    | m2_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62,X1_62)
    | ~ l1_waybel_0(X1_62,X0_62)
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X1_62)
    | ~ v7_waybel_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1470,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | m2_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62,X1_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_1458,plain,
    ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X2_62,X1_62) != iProver_top
    | l1_waybel_0(X0_62,X1_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X2_62) = iProver_top
    | v4_orders_2(X2_62) != iProver_top
    | v7_waybel_0(X2_62) != iProver_top
    | l1_struct_0(X1_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_6131,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top
    | l1_struct_0(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1458])).

cnf(c_7022,plain,
    ( l1_pre_topc(X0_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | l1_waybel_0(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6131,c_566])).

cnf(c_7023,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | l1_waybel_0(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_7022])).

cnf(c_18,plain,
    ( v3_yellow_6(X0,X1)
    | ~ l1_waybel_0(X0,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1)
    | k10_yellow_6(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_494,plain,
    ( v3_yellow_6(X0_62,X1_62)
    | ~ l1_waybel_0(X0_62,X1_62)
    | ~ v2_pre_topc(X1_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62)
    | ~ l1_pre_topc(X1_62)
    | k10_yellow_6(X1_62,X0_62) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1463,plain,
    ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
    | v3_yellow_6(X1_62,X0_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_7041,plain,
    ( k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)) = k1_xboole_0
    | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | v3_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(sK4(X0_62,X1_62,X2_62)) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_7023,c_1463])).

cnf(c_6132,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(sK4(X0_62,X1_62,X2_62)) = iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top
    | l1_struct_0(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1460])).

cnf(c_6851,plain,
    ( l1_pre_topc(X0_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v4_orders_2(sK4(X0_62,X1_62,X2_62)) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6132,c_566])).

cnf(c_6852,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v4_orders_2(sK4(X0_62,X1_62,X2_62)) = iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_6851])).

cnf(c_6133,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top
    | l1_struct_0(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1459])).

cnf(c_6935,plain,
    ( l1_pre_topc(X0_62) != iProver_top
    | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6133,c_566])).

cnf(c_6936,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_6935])).

cnf(c_6130,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top
    | l1_struct_0(X0_62) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1461])).

cnf(c_6952,plain,
    ( l1_pre_topc(X0_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v2_struct_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6130,c_566])).

cnf(c_6953,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_6952])).

cnf(c_8450,plain,
    ( v7_waybel_0(X1_62) != iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | v3_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
    | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)) = k1_xboole_0
    | v4_orders_2(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7041,c_6852,c_6936,c_6953])).

cnf(c_8451,plain,
    ( k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)) = k1_xboole_0
    | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | v3_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(renaming,[status(thm)],[c_8450])).

cnf(c_41,negated_conjecture,
    ( ~ m2_yellow_6(X0,sK9,sK10)
    | ~ v3_yellow_6(X0,sK9)
    | ~ v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_471,negated_conjecture,
    ( ~ m2_yellow_6(X0_62,sK9,sK10)
    | ~ v3_yellow_6(X0_62,sK9)
    | ~ v1_compts_1(sK9) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_1486,plain,
    ( m2_yellow_6(X0_62,sK9,sK10) != iProver_top
    | v3_yellow_6(X0_62,sK9) != iProver_top
    | v1_compts_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_6129,plain,
    ( r3_waybel_9(sK9,sK10,X0_62) != iProver_top
    | v3_yellow_6(sK4(sK9,sK10,X0_62),sK9) != iProver_top
    | l1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v1_compts_1(sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1470,c_1486])).

cnf(c_45,negated_conjecture,
    ( ~ v1_compts_1(sK9)
    | ~ v2_struct_0(sK10) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_60,plain,
    ( v1_compts_1(sK9) != iProver_top
    | v2_struct_0(sK10) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( ~ v1_compts_1(sK9)
    | v4_orders_2(sK10) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_61,plain,
    ( v1_compts_1(sK9) != iProver_top
    | v4_orders_2(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_43,negated_conjecture,
    ( ~ v1_compts_1(sK9)
    | v7_waybel_0(sK10) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_62,plain,
    ( v1_compts_1(sK9) != iProver_top
    | v7_waybel_0(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_42,negated_conjecture,
    ( l1_waybel_0(sK10,sK9)
    | ~ v1_compts_1(sK9) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_63,plain,
    ( l1_waybel_0(sK10,sK9) = iProver_top
    | v1_compts_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_6524,plain,
    ( v3_yellow_6(sK4(sK9,sK10,X0_62),sK9) != iProver_top
    | r3_waybel_9(sK9,sK10,X0_62) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v1_compts_1(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6129,c_51,c_52,c_53,c_60,c_61,c_62,c_63])).

cnf(c_6525,plain,
    ( r3_waybel_9(sK9,sK10,X0_62) != iProver_top
    | v3_yellow_6(sK4(sK9,sK10,X0_62),sK9) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v1_compts_1(sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_6524])).

cnf(c_8467,plain,
    ( k10_yellow_6(sK9,sK4(sK9,sK10,X0_62)) = k1_xboole_0
    | r3_waybel_9(sK9,sK10,X0_62) != iProver_top
    | l1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v1_compts_1(sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_8451,c_6525])).

cnf(c_9138,plain,
    ( r3_waybel_9(sK9,sK10,X0_62) != iProver_top
    | k10_yellow_6(sK9,sK4(sK9,sK10,X0_62)) = k1_xboole_0
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v1_compts_1(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8467,c_51,c_52,c_53,c_60,c_61,c_62,c_63])).

cnf(c_9139,plain,
    ( k10_yellow_6(sK9,sK4(sK9,sK10,X0_62)) = k1_xboole_0
    | r3_waybel_9(sK9,sK10,X0_62) != iProver_top
    | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
    | v1_compts_1(sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_9138])).

cnf(c_9149,plain,
    ( k10_yellow_6(sK9,sK4(sK9,sK10,sK6(sK9,sK10))) = k1_xboole_0
    | l1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK6(sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | v1_compts_1(sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1476,c_9139])).

cnf(c_32,plain,
    ( ~ l1_waybel_0(X0,X1)
    | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
    | ~ v1_compts_1(X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_480,plain,
    ( ~ l1_waybel_0(X0_62,X1_62)
    | m1_subset_1(sK6(X1_62,X0_62),u1_struct_0(X1_62))
    | ~ v1_compts_1(X1_62)
    | ~ v2_pre_topc(X1_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X0_62)
    | ~ v7_waybel_0(X0_62)
    | ~ l1_pre_topc(X1_62) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2398,plain,
    ( ~ l1_waybel_0(sK10,X0_62)
    | m1_subset_1(sK6(X0_62,sK10),u1_struct_0(X0_62))
    | ~ v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(sK10)
    | ~ v4_orders_2(sK10)
    | ~ v7_waybel_0(sK10)
    | ~ l1_pre_topc(X0_62) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_2399,plain,
    ( l1_waybel_0(sK10,X0_62) != iProver_top
    | m1_subset_1(sK6(X0_62,sK10),u1_struct_0(X0_62)) = iProver_top
    | v1_compts_1(X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_2401,plain,
    ( l1_waybel_0(sK10,sK9) != iProver_top
    | m1_subset_1(sK6(sK9,sK10),u1_struct_0(sK9)) = iProver_top
    | v1_compts_1(sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2399])).

cnf(c_9361,plain,
    ( k10_yellow_6(sK9,sK4(sK9,sK10,sK6(sK9,sK10))) = k1_xboole_0
    | v1_compts_1(sK9) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9149,c_51,c_52,c_53,c_60,c_61,c_62,c_63,c_2401])).

cnf(c_20654,plain,
    ( k10_yellow_6(sK9,sK4(sK9,sK10,sK6(sK9,sK10))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20646,c_9361])).

cnf(c_24,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_488,plain,
    ( ~ r3_waybel_9(X0_62,X1_62,X2_62)
    | ~ l1_waybel_0(X1_62,X0_62)
    | r2_hidden(X2_62,k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)))
    | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(X1_62)
    | ~ v4_orders_2(X1_62)
    | ~ v7_waybel_0(X1_62)
    | ~ l1_pre_topc(X0_62) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1469,plain,
    ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
    | l1_waybel_0(X1_62,X0_62) != iProver_top
    | r2_hidden(X2_62,k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62))) = iProver_top
    | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(X1_62) = iProver_top
    | v4_orders_2(X1_62) != iProver_top
    | v7_waybel_0(X1_62) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_21502,plain,
    ( r3_waybel_9(sK9,sK10,sK6(sK9,sK10)) != iProver_top
    | l1_waybel_0(sK10,sK9) != iProver_top
    | r2_hidden(sK6(sK9,sK10),k1_xboole_0) = iProver_top
    | m1_subset_1(sK6(sK9,sK10),u1_struct_0(sK9)) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_20654,c_1469])).

cnf(c_2439,plain,
    ( r3_waybel_9(X0_62,sK10,sK6(X0_62,sK10))
    | ~ l1_waybel_0(sK10,X0_62)
    | ~ v1_compts_1(X0_62)
    | ~ v2_pre_topc(X0_62)
    | v2_struct_0(X0_62)
    | v2_struct_0(sK10)
    | ~ v4_orders_2(sK10)
    | ~ v7_waybel_0(sK10)
    | ~ l1_pre_topc(X0_62) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2440,plain,
    ( r3_waybel_9(X0_62,sK10,sK6(X0_62,sK10)) = iProver_top
    | l1_waybel_0(sK10,X0_62) != iProver_top
    | v1_compts_1(X0_62) != iProver_top
    | v2_pre_topc(X0_62) != iProver_top
    | v2_struct_0(X0_62) = iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(X0_62) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2439])).

cnf(c_2442,plain,
    ( r3_waybel_9(sK9,sK10,sK6(sK9,sK10)) = iProver_top
    | l1_waybel_0(sK10,sK9) != iProver_top
    | v1_compts_1(sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top
    | v2_struct_0(sK10) = iProver_top
    | v2_struct_0(sK9) = iProver_top
    | v4_orders_2(sK10) != iProver_top
    | v7_waybel_0(sK10) != iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2440])).

cnf(c_22996,plain,
    ( r2_hidden(sK6(sK9,sK10),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21502,c_51,c_52,c_53,c_60,c_61,c_62,c_63,c_75,c_78,c_81,c_84,c_167,c_2401,c_2442,c_2695,c_2699,c_2962,c_3012,c_3689,c_4563,c_4712,c_20601])).

cnf(c_23001,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK9,sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22996,c_1448])).

cnf(c_23866,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23001,c_1445])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:41:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.89/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.89/1.48  
% 7.89/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.89/1.48  
% 7.89/1.48  ------  iProver source info
% 7.89/1.48  
% 7.89/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.89/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.89/1.48  git: non_committed_changes: false
% 7.89/1.48  git: last_make_outside_of_git: false
% 7.89/1.48  
% 7.89/1.48  ------ 
% 7.89/1.48  ------ Parsing...
% 7.89/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.89/1.48  
% 7.89/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.89/1.48  
% 7.89/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.89/1.48  
% 7.89/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.89/1.48  ------ Proving...
% 7.89/1.48  ------ Problem Properties 
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  clauses                                 51
% 7.89/1.48  conjectures                             10
% 7.89/1.48  EPR                                     16
% 7.89/1.48  Horn                                    13
% 7.89/1.48  unary                                   5
% 7.89/1.48  binary                                  6
% 7.89/1.48  lits                                    330
% 7.89/1.48  lits eq                                 6
% 7.89/1.48  fd_pure                                 0
% 7.89/1.48  fd_pseudo                               0
% 7.89/1.48  fd_cond                                 0
% 7.89/1.48  fd_pseudo_cond                          4
% 7.89/1.48  AC symbols                              0
% 7.89/1.48  
% 7.89/1.48  ------ Input Options Time Limit: Unbounded
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  ------ 
% 7.89/1.48  Current options:
% 7.89/1.48  ------ 
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  ------ Proving...
% 7.89/1.48  
% 7.89/1.48  
% 7.89/1.48  % SZS status Theorem for theBenchmark.p
% 7.89/1.48  
% 7.89/1.48   Resolution empty clause
% 7.89/1.48  
% 7.89/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.89/1.48  
% 7.89/1.48  fof(f16,conjecture,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f17,negated_conjecture,(
% 7.89/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)))))),
% 7.89/1.48    inference(negated_conjecture,[],[f16])).
% 7.89/1.48  
% 7.89/1.48  fof(f42,plain,(
% 7.89/1.48    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f17])).
% 7.89/1.48  
% 7.89/1.48  fof(f43,plain,(
% 7.89/1.48    ? [X0] : ((v1_compts_1(X0) <~> ! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f42])).
% 7.89/1.48  
% 7.89/1.48  fof(f68,plain,(
% 7.89/1.48    ? [X0] : (((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.89/1.48    inference(nnf_transformation,[],[f43])).
% 7.89/1.48  
% 7.89/1.48  fof(f69,plain,(
% 7.89/1.48    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X1] : (? [X2] : (v3_yellow_6(X2,X0) & m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f68])).
% 7.89/1.48  
% 7.89/1.48  fof(f70,plain,(
% 7.89/1.48    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.89/1.48    inference(rectify,[],[f69])).
% 7.89/1.48  
% 7.89/1.48  fof(f73,plain,(
% 7.89/1.48    ( ! [X0] : (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) => (v3_yellow_6(sK11(X3),X0) & m2_yellow_6(sK11(X3),X0,X3)))) )),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f72,plain,(
% 7.89/1.48    ( ! [X0] : (? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,sK10)) & l1_waybel_0(sK10,X0) & v7_waybel_0(sK10) & v4_orders_2(sK10) & ~v2_struct_0(sK10))) )),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f71,plain,(
% 7.89/1.48    ? [X0] : ((? [X1] : (! [X2] : (~v3_yellow_6(X2,X0) | ~m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(X0)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,X0) & m2_yellow_6(X4,X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ((? [X1] : (! [X2] : (~v3_yellow_6(X2,sK9) | ~m2_yellow_6(X2,sK9,X1)) & l1_waybel_0(X1,sK9) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) | ~v1_compts_1(sK9)) & (! [X3] : (? [X4] : (v3_yellow_6(X4,sK9) & m2_yellow_6(X4,sK9,X3)) | ~l1_waybel_0(X3,sK9) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK9)) & l1_pre_topc(sK9) & v2_pre_topc(sK9) & ~v2_struct_0(sK9))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f74,plain,(
% 7.89/1.48    ((! [X2] : (~v3_yellow_6(X2,sK9) | ~m2_yellow_6(X2,sK9,sK10)) & l1_waybel_0(sK10,sK9) & v7_waybel_0(sK10) & v4_orders_2(sK10) & ~v2_struct_0(sK10)) | ~v1_compts_1(sK9)) & (! [X3] : ((v3_yellow_6(sK11(X3),sK9) & m2_yellow_6(sK11(X3),sK9,X3)) | ~l1_waybel_0(X3,sK9) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | v1_compts_1(sK9)) & l1_pre_topc(sK9) & v2_pre_topc(sK9) & ~v2_struct_0(sK9)),
% 7.89/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f70,f73,f72,f71])).
% 7.89/1.48  
% 7.89/1.48  fof(f119,plain,(
% 7.89/1.48    ( ! [X3] : (m2_yellow_6(sK11(X3),sK9,X3) | ~l1_waybel_0(X3,sK9) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK9)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f11,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> ! [X3] : (m1_connsp_2(X3,X0,X2) => r2_waybel_0(X0,X1,X3))))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f32,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f11])).
% 7.89/1.48  
% 7.89/1.48  fof(f33,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> ! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f32])).
% 7.89/1.48  
% 7.89/1.48  fof(f52,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X3] : (r2_waybel_0(X0,X1,X3) | ~m1_connsp_2(X3,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(nnf_transformation,[],[f33])).
% 7.89/1.48  
% 7.89/1.48  fof(f53,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(rectify,[],[f52])).
% 7.89/1.48  
% 7.89/1.48  fof(f54,plain,(
% 7.89/1.48    ! [X2,X1,X0] : (? [X3] : (~r2_waybel_0(X0,X1,X3) & m1_connsp_2(X3,X0,X2)) => (~r2_waybel_0(X0,X1,sK3(X0,X1,X2)) & m1_connsp_2(sK3(X0,X1,X2),X0,X2)))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f55,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | (~r2_waybel_0(X0,X1,sK3(X0,X1,X2)) & m1_connsp_2(sK3(X0,X1,X2),X0,X2))) & (! [X4] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2)) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f53,f54])).
% 7.89/1.48  
% 7.89/1.48  fof(f96,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | m1_connsp_2(sK3(X0,X1,X2),X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f55])).
% 7.89/1.48  
% 7.89/1.48  fof(f1,axiom,(
% 7.89/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f75,plain,(
% 7.89/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f1])).
% 7.89/1.48  
% 7.89/1.48  fof(f6,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f22,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f6])).
% 7.89/1.48  
% 7.89/1.48  fof(f23,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f22])).
% 7.89/1.48  
% 7.89/1.48  fof(f44,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(nnf_transformation,[],[f23])).
% 7.89/1.48  
% 7.89/1.48  fof(f45,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f44])).
% 7.89/1.48  
% 7.89/1.48  fof(f46,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(rectify,[],[f45])).
% 7.89/1.48  
% 7.89/1.48  fof(f49,plain,(
% 7.89/1.48    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6)))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f48,plain,(
% 7.89/1.48    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) => (~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,X3)))) )),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f47,plain,(
% 7.89/1.48    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f50,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK1(X0,X1,X2)) & m1_connsp_2(sK1(X0,X1,X2),X0,sK0(X0,X1,X2))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2))) | r2_hidden(sK0(X0,X1,X2),X2)) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) & m1_connsp_2(sK2(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f49,f48,f47])).
% 7.89/1.48  
% 7.89/1.48  fof(f81,plain,(
% 7.89/1.48    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f50])).
% 7.89/1.48  
% 7.89/1.48  fof(f127,plain,(
% 7.89/1.48    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | m1_connsp_2(sK2(X0,X1,X6),X0,X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(equality_resolution,[],[f81])).
% 7.89/1.48  
% 7.89/1.48  fof(f7,axiom,(
% 7.89/1.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f24,plain,(
% 7.89/1.48    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f7])).
% 7.89/1.48  
% 7.89/1.48  fof(f25,plain,(
% 7.89/1.48    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f24])).
% 7.89/1.48  
% 7.89/1.48  fof(f87,plain,(
% 7.89/1.48    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f25])).
% 7.89/1.48  
% 7.89/1.48  fof(f84,plain,(
% 7.89/1.48    ( ! [X2,X0,X5,X1] : (k10_yellow_6(X0,X1) = X2 | r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK0(X0,X1,X2)) | r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f50])).
% 7.89/1.48  
% 7.89/1.48  fof(f83,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (k10_yellow_6(X0,X1) = X2 | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f50])).
% 7.89/1.48  
% 7.89/1.48  fof(f4,axiom,(
% 7.89/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f20,plain,(
% 7.89/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.89/1.48    inference(ennf_transformation,[],[f4])).
% 7.89/1.48  
% 7.89/1.48  fof(f78,plain,(
% 7.89/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f20])).
% 7.89/1.48  
% 7.89/1.48  fof(f2,axiom,(
% 7.89/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f76,plain,(
% 7.89/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.89/1.48    inference(cnf_transformation,[],[f2])).
% 7.89/1.48  
% 7.89/1.48  fof(f82,plain,(
% 7.89/1.48    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,X2) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f50])).
% 7.89/1.48  
% 7.89/1.48  fof(f126,plain,(
% 7.89/1.48    ( ! [X6,X0,X1] : (r2_hidden(X6,k10_yellow_6(X0,X1)) | ~r1_waybel_0(X0,X1,sK2(X0,X1,X6)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(equality_resolution,[],[f82])).
% 7.89/1.48  
% 7.89/1.48  fof(f12,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) => r3_waybel_9(X0,X1,X2)))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f34,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f12])).
% 7.89/1.48  
% 7.89/1.48  fof(f35,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f34])).
% 7.89/1.48  
% 7.89/1.48  fof(f98,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f35])).
% 7.89/1.48  
% 7.89/1.48  fof(f3,axiom,(
% 7.89/1.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f18,plain,(
% 7.89/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.89/1.48    inference(ennf_transformation,[],[f3])).
% 7.89/1.48  
% 7.89/1.48  fof(f19,plain,(
% 7.89/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.89/1.48    inference(flattening,[],[f18])).
% 7.89/1.48  
% 7.89/1.48  fof(f77,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f19])).
% 7.89/1.48  
% 7.89/1.48  fof(f95,plain,(
% 7.89/1.48    ( ! [X4,X2,X0,X1] : (r2_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f55])).
% 7.89/1.48  
% 7.89/1.48  fof(f9,axiom,(
% 7.89/1.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f28,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f9])).
% 7.89/1.48  
% 7.89/1.48  fof(f29,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f28])).
% 7.89/1.48  
% 7.89/1.48  fof(f92,plain,(
% 7.89/1.48    ( ! [X2,X0,X3,X1] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f29])).
% 7.89/1.48  
% 7.89/1.48  fof(f5,axiom,(
% 7.89/1.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f21,plain,(
% 7.89/1.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.89/1.48    inference(ennf_transformation,[],[f5])).
% 7.89/1.48  
% 7.89/1.48  fof(f79,plain,(
% 7.89/1.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f21])).
% 7.89/1.48  
% 7.89/1.48  fof(f97,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r2_waybel_0(X0,X1,sK3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f55])).
% 7.89/1.48  
% 7.89/1.48  fof(f15,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ~(! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~r3_waybel_9(X0,X1,X2)) & r2_hidden(X1,k6_yellow_6(X0))))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f40,plain,(
% 7.89/1.48    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : ((? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f15])).
% 7.89/1.48  
% 7.89/1.48  fof(f41,plain,(
% 7.89/1.48    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f40])).
% 7.89/1.48  
% 7.89/1.48  fof(f63,plain,(
% 7.89/1.48    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~r2_hidden(X1,k6_yellow_6(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(nnf_transformation,[],[f41])).
% 7.89/1.48  
% 7.89/1.48  fof(f64,plain,(
% 7.89/1.48    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(rectify,[],[f63])).
% 7.89/1.48  
% 7.89/1.48  fof(f66,plain,(
% 7.89/1.48    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK8(X0,X3)) & m1_subset_1(sK8(X0,X3),u1_struct_0(X0))))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f65,plain,(
% 7.89/1.48    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(X1,k6_yellow_6(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK7(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK7(X0),k6_yellow_6(X0)) & l1_waybel_0(sK7(X0),X0) & v7_waybel_0(sK7(X0)) & v4_orders_2(sK7(X0)) & ~v2_struct_0(sK7(X0))))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f67,plain,(
% 7.89/1.48    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK7(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & r2_hidden(sK7(X0),k6_yellow_6(X0)) & l1_waybel_0(sK7(X0),X0) & v7_waybel_0(sK7(X0)) & v4_orders_2(sK7(X0)) & ~v2_struct_0(sK7(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK8(X0,X3)) & m1_subset_1(sK8(X0,X3),u1_struct_0(X0))) | ~r2_hidden(X3,k6_yellow_6(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f64,f66,f65])).
% 7.89/1.48  
% 7.89/1.48  fof(f115,plain,(
% 7.89/1.48    ( ! [X2,X0] : (v1_compts_1(X0) | ~r3_waybel_9(X0,sK7(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f67])).
% 7.89/1.48  
% 7.89/1.48  fof(f113,plain,(
% 7.89/1.48    ( ! [X0] : (v1_compts_1(X0) | l1_waybel_0(sK7(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f67])).
% 7.89/1.48  
% 7.89/1.48  fof(f112,plain,(
% 7.89/1.48    ( ! [X0] : (v1_compts_1(X0) | v7_waybel_0(sK7(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f67])).
% 7.89/1.48  
% 7.89/1.48  fof(f111,plain,(
% 7.89/1.48    ( ! [X0] : (v1_compts_1(X0) | v4_orders_2(sK7(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f67])).
% 7.89/1.48  
% 7.89/1.48  fof(f110,plain,(
% 7.89/1.48    ( ! [X0] : (v1_compts_1(X0) | ~v2_struct_0(sK7(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f67])).
% 7.89/1.48  
% 7.89/1.48  fof(f116,plain,(
% 7.89/1.48    ~v2_struct_0(sK9)),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f117,plain,(
% 7.89/1.48    v2_pre_topc(sK9)),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f118,plain,(
% 7.89/1.48    l1_pre_topc(sK9)),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f120,plain,(
% 7.89/1.48    ( ! [X3] : (v3_yellow_6(sK11(X3),sK9) | ~l1_waybel_0(X3,sK9) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | v1_compts_1(sK9)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f10,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f30,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f10])).
% 7.89/1.48  
% 7.89/1.48  fof(f31,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : ((v3_yellow_6(X1,X0) <=> k1_xboole_0 != k10_yellow_6(X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f30])).
% 7.89/1.48  
% 7.89/1.48  fof(f51,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (((v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1)) & (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(nnf_transformation,[],[f31])).
% 7.89/1.48  
% 7.89/1.48  fof(f93,plain,(
% 7.89/1.48    ( ! [X0,X1] : (k1_xboole_0 != k10_yellow_6(X0,X1) | ~v3_yellow_6(X1,X0) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f51])).
% 7.89/1.48  
% 7.89/1.48  fof(f8,axiom,(
% 7.89/1.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f26,plain,(
% 7.89/1.48    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f8])).
% 7.89/1.48  
% 7.89/1.48  fof(f27,plain,(
% 7.89/1.48    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f26])).
% 7.89/1.48  
% 7.89/1.48  fof(f91,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (l1_waybel_0(X2,X0) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f27])).
% 7.89/1.48  
% 7.89/1.48  fof(f90,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (v7_waybel_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f27])).
% 7.89/1.48  
% 7.89/1.48  fof(f89,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (v4_orders_2(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f27])).
% 7.89/1.48  
% 7.89/1.48  fof(f88,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (~v2_struct_0(X2) | ~m2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f27])).
% 7.89/1.48  
% 7.89/1.48  fof(f14,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_compts_1(X0) <=> ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f38,plain,(
% 7.89/1.48    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f14])).
% 7.89/1.48  
% 7.89/1.48  fof(f39,plain,(
% 7.89/1.48    ! [X0] : ((v1_compts_1(X0) <=> ! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f38])).
% 7.89/1.48  
% 7.89/1.48  fof(f58,plain,(
% 7.89/1.48    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X1] : (? [X2] : (r3_waybel_9(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(nnf_transformation,[],[f39])).
% 7.89/1.48  
% 7.89/1.48  fof(f59,plain,(
% 7.89/1.48    ! [X0] : (((v1_compts_1(X0) | ? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (! [X3] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(rectify,[],[f58])).
% 7.89/1.48  
% 7.89/1.48  fof(f61,plain,(
% 7.89/1.48    ! [X3,X0] : (? [X4] : (r3_waybel_9(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f60,plain,(
% 7.89/1.48    ! [X0] : (? [X1] : (! [X2] : (~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0))))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f62,plain,(
% 7.89/1.48    ! [X0] : (((v1_compts_1(X0) | (! [X2] : (~r3_waybel_9(X0,sK5(X0),X2) | ~m1_subset_1(X2,u1_struct_0(X0))) & l1_waybel_0(sK5(X0),X0) & v7_waybel_0(sK5(X0)) & v4_orders_2(sK5(X0)) & ~v2_struct_0(sK5(X0)))) & (! [X3] : ((r3_waybel_9(X0,X3,sK6(X0,X3)) & m1_subset_1(sK6(X0,X3),u1_struct_0(X0))) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f59,f61,f60])).
% 7.89/1.48  
% 7.89/1.48  fof(f102,plain,(
% 7.89/1.48    ( ! [X0,X3] : (r3_waybel_9(X0,X3,sK6(X0,X3)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f62])).
% 7.89/1.48  
% 7.89/1.48  fof(f13,axiom,(
% 7.89/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m2_yellow_6(X3,X0,X1) => ~r2_hidden(X2,k10_yellow_6(X0,X3))) & r3_waybel_9(X0,X1,X2)))))),
% 7.89/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.89/1.48  
% 7.89/1.48  fof(f36,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.89/1.48    inference(ennf_transformation,[],[f13])).
% 7.89/1.48  
% 7.89/1.48  fof(f37,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(flattening,[],[f36])).
% 7.89/1.48  
% 7.89/1.48  fof(f56,plain,(
% 7.89/1.48    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,k10_yellow_6(X0,X3)) & m2_yellow_6(X3,X0,X1)) => (r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2))) & m2_yellow_6(sK4(X0,X1,X2),X0,X1)))),
% 7.89/1.48    introduced(choice_axiom,[])).
% 7.89/1.48  
% 7.89/1.48  fof(f57,plain,(
% 7.89/1.48    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2))) & m2_yellow_6(sK4(X0,X1,X2),X0,X1)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.89/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f56])).
% 7.89/1.48  
% 7.89/1.48  fof(f99,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (m2_yellow_6(sK4(X0,X1,X2),X0,X1) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f57])).
% 7.89/1.48  
% 7.89/1.48  fof(f94,plain,(
% 7.89/1.48    ( ! [X0,X1] : (v3_yellow_6(X1,X0) | k1_xboole_0 = k10_yellow_6(X0,X1) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f51])).
% 7.89/1.48  
% 7.89/1.48  fof(f125,plain,(
% 7.89/1.48    ( ! [X2] : (~v3_yellow_6(X2,sK9) | ~m2_yellow_6(X2,sK9,sK10) | ~v1_compts_1(sK9)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f121,plain,(
% 7.89/1.48    ~v2_struct_0(sK10) | ~v1_compts_1(sK9)),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f122,plain,(
% 7.89/1.48    v4_orders_2(sK10) | ~v1_compts_1(sK9)),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f123,plain,(
% 7.89/1.48    v7_waybel_0(sK10) | ~v1_compts_1(sK9)),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f124,plain,(
% 7.89/1.48    l1_waybel_0(sK10,sK9) | ~v1_compts_1(sK9)),
% 7.89/1.48    inference(cnf_transformation,[],[f74])).
% 7.89/1.48  
% 7.89/1.48  fof(f101,plain,(
% 7.89/1.48    ( ! [X0,X3] : (m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) | ~l1_waybel_0(X3,X0) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3) | ~v1_compts_1(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f62])).
% 7.89/1.48  
% 7.89/1.48  fof(f100,plain,(
% 7.89/1.48    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2))) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.89/1.48    inference(cnf_transformation,[],[f57])).
% 7.89/1.48  
% 7.89/1.48  cnf(c_47,negated_conjecture,
% 7.89/1.48      ( m2_yellow_6(sK11(X0),sK9,X0)
% 7.89/1.48      | ~ l1_waybel_0(X0,sK9)
% 7.89/1.48      | v1_compts_1(sK9)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | ~ v4_orders_2(X0)
% 7.89/1.48      | ~ v7_waybel_0(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f119]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_465,negated_conjecture,
% 7.89/1.48      ( m2_yellow_6(sK11(X0_62),sK9,X0_62)
% 7.89/1.48      | ~ l1_waybel_0(X0_62,sK9)
% 7.89/1.48      | v1_compts_1(sK9)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | ~ v4_orders_2(X0_62)
% 7.89/1.48      | ~ v7_waybel_0(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_47]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1492,plain,
% 7.89/1.48      ( m2_yellow_6(sK11(X0_62),sK9,X0_62) = iProver_top
% 7.89/1.48      | l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.48      | v1_compts_1(sK9) = iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_21,plain,
% 7.89/1.48      ( r3_waybel_9(X0,X1,X2)
% 7.89/1.48      | m1_connsp_2(sK3(X0,X1,X2),X0,X2)
% 7.89/1.48      | ~ l1_waybel_0(X1,X0)
% 7.89/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.48      | ~ v2_pre_topc(X0)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | ~ l1_pre_topc(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_491,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62)
% 7.89/1.48      | m1_connsp_2(sK3(X0_62,X1_62,X2_62),X0_62,X2_62)
% 7.89/1.48      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.48      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.48      | ~ v2_pre_topc(X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_21]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1466,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
% 7.89/1.48      | m1_connsp_2(sK3(X0_62,X1_62,X2_62),X0_62,X2_62) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_0,plain,
% 7.89/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_512,plain,
% 7.89/1.48      ( r1_tarski(k1_xboole_0,X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1445,plain,
% 7.89/1.48      ( r1_tarski(k1_xboole_0,X0_62) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10,plain,
% 7.89/1.48      ( m1_connsp_2(sK2(X0,X1,X2),X0,X2)
% 7.89/1.48      | ~ l1_waybel_0(X1,X0)
% 7.89/1.48      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.89/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.48      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.89/1.48      | ~ v2_pre_topc(X0)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | ~ v4_orders_2(X1)
% 7.89/1.48      | ~ v7_waybel_0(X1)
% 7.89/1.48      | ~ l1_pre_topc(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f127]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_502,plain,
% 7.89/1.48      ( m1_connsp_2(sK2(X0_62,X1_62,X2_62),X0_62,X2_62)
% 7.89/1.48      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62))
% 7.89/1.48      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.48      | ~ m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62)))
% 7.89/1.48      | ~ v2_pre_topc(X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ v4_orders_2(X1_62)
% 7.89/1.48      | ~ v7_waybel_0(X1_62)
% 7.89/1.48      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1455,plain,
% 7.89/1.48      ( m1_connsp_2(sK2(X0_62,X1_62,X2_62),X0_62,X2_62) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_12,plain,
% 7.89/1.48      ( ~ l1_waybel_0(X0,X1)
% 7.89/1.48      | m1_subset_1(k10_yellow_6(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.89/1.48      | ~ v2_pre_topc(X1)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | ~ v4_orders_2(X0)
% 7.89/1.48      | ~ v7_waybel_0(X0)
% 7.89/1.48      | ~ l1_pre_topc(X1) ),
% 7.89/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_500,plain,
% 7.89/1.48      ( ~ l1_waybel_0(X0_62,X1_62)
% 7.89/1.48      | m1_subset_1(k10_yellow_6(X1_62,X0_62),k1_zfmisc_1(u1_struct_0(X1_62)))
% 7.89/1.48      | ~ v2_pre_topc(X1_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ v4_orders_2(X0_62)
% 7.89/1.48      | ~ v7_waybel_0(X0_62)
% 7.89/1.48      | ~ l1_pre_topc(X1_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_12]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1457,plain,
% 7.89/1.48      ( l1_waybel_0(X0_62,X1_62) != iProver_top
% 7.89/1.48      | m1_subset_1(k10_yellow_6(X1_62,X0_62),k1_zfmisc_1(u1_struct_0(X1_62))) = iProver_top
% 7.89/1.48      | v2_pre_topc(X1_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X0_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X1_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2053,plain,
% 7.89/1.48      ( m1_connsp_2(sK2(X0_62,X1_62,X2_62),X0_62,X2_62) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_1455,c_1457]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_7,plain,
% 7.89/1.48      ( ~ m1_connsp_2(X0,X1,sK0(X1,X2,X3))
% 7.89/1.48      | r1_waybel_0(X1,X2,X0)
% 7.89/1.48      | ~ l1_waybel_0(X2,X1)
% 7.89/1.48      | r2_hidden(sK0(X1,X2,X3),X3)
% 7.89/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 7.89/1.48      | ~ v2_pre_topc(X1)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | v2_struct_0(X2)
% 7.89/1.48      | ~ v4_orders_2(X2)
% 7.89/1.48      | ~ v7_waybel_0(X2)
% 7.89/1.48      | ~ l1_pre_topc(X1)
% 7.89/1.48      | k10_yellow_6(X1,X2) = X3 ),
% 7.89/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_505,plain,
% 7.89/1.48      ( ~ m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,X2_62))
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,X0_64)
% 7.89/1.48      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62)
% 7.89/1.48      | ~ m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62)))
% 7.89/1.48      | ~ v2_pre_topc(X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ v4_orders_2(X1_62)
% 7.89/1.48      | ~ v7_waybel_0(X1_62)
% 7.89/1.48      | ~ l1_pre_topc(X0_62)
% 7.89/1.48      | k10_yellow_6(X0_62,X1_62) = X2_62 ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1452,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = X2_62
% 7.89/1.48      | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,X0_64) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_6545,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = X2_62
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
% 7.89/1.48      | l1_waybel_0(X3_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | m1_subset_1(sK0(X0_62,X1_62,X2_62),u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X3_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X3_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X3_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_2053,c_1452]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_8,plain,
% 7.89/1.48      ( ~ l1_waybel_0(X0,X1)
% 7.89/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.89/1.48      | m1_subset_1(sK0(X1,X0,X2),u1_struct_0(X1))
% 7.89/1.48      | ~ v2_pre_topc(X1)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | ~ v4_orders_2(X0)
% 7.89/1.48      | ~ v7_waybel_0(X0)
% 7.89/1.48      | ~ l1_pre_topc(X1)
% 7.89/1.48      | k10_yellow_6(X1,X0) = X2 ),
% 7.89/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_504,plain,
% 7.89/1.48      ( ~ l1_waybel_0(X0_62,X1_62)
% 7.89/1.48      | ~ m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X1_62)))
% 7.89/1.48      | m1_subset_1(sK0(X1_62,X0_62,X2_62),u1_struct_0(X1_62))
% 7.89/1.48      | ~ v2_pre_topc(X1_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ v4_orders_2(X0_62)
% 7.89/1.48      | ~ v7_waybel_0(X0_62)
% 7.89/1.48      | ~ l1_pre_topc(X1_62)
% 7.89/1.48      | k10_yellow_6(X1_62,X0_62) = X2_62 ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_576,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = X2_62
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | m1_subset_1(sK0(X0_62,X1_62,X2_62),u1_struct_0(X0_62)) = iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_9911,plain,
% 7.89/1.48      ( m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X3_62,X0_62) != iProver_top
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
% 7.89/1.48      | k10_yellow_6(X0_62,X1_62) = X2_62
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X3_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X3_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X3_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(global_propositional_subsumption,[status(thm)],[c_6545,c_576]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_9912,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = X2_62
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X3_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),X2_62) = iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X3_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X3_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X3_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(renaming,[status(thm)],[c_9911]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_3,plain,
% 7.89/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_509,plain,
% 7.89/1.48      ( ~ r2_hidden(X0_62,X1_62) | ~ r1_tarski(X1_62,X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1448,plain,
% 7.89/1.48      ( r2_hidden(X0_62,X1_62) != iProver_top
% 7.89/1.48      | r1_tarski(X1_62,X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_9935,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = X2_62
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X3_62,sK0(X0_62,X1_62,X2_62))) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X3_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,X2_62),k10_yellow_6(X0_62,X3_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | r1_tarski(X2_62,sK0(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X3_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X3_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X3_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_9912,c_1448]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10382,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X2_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_1445,c_9935]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1,plain,
% 7.89/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.89/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_511,plain,
% 7.89/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_63)) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2487,plain,
% 7.89/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) ),
% 7.89/1.48      inference(instantiation,[status(thm)],[c_511]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2489,plain,
% 7.89/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_2487]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10491,plain,
% 7.89/1.48      ( r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X2_62)) = iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(global_propositional_subsumption,
% 7.89/1.48                [status(thm)],
% 7.89/1.48                [c_10382,c_2489]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10492,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r1_waybel_0(X0_62,X1_62,sK2(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X2_62)) = iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(renaming,[status(thm)],[c_10491]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_9,plain,
% 7.89/1.48      ( ~ r1_waybel_0(X0,X1,sK2(X0,X1,X2))
% 7.89/1.48      | ~ l1_waybel_0(X1,X0)
% 7.89/1.48      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.89/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.48      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 7.89/1.48      | ~ v2_pre_topc(X0)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | ~ v4_orders_2(X1)
% 7.89/1.48      | ~ v7_waybel_0(X1)
% 7.89/1.48      | ~ l1_pre_topc(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f126]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_503,plain,
% 7.89/1.48      ( ~ r1_waybel_0(X0_62,X1_62,sK2(X0_62,X1_62,X2_62))
% 7.89/1.48      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62))
% 7.89/1.48      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.48      | ~ m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62)))
% 7.89/1.48      | ~ v2_pre_topc(X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ v4_orders_2(X1_62)
% 7.89/1.48      | ~ v7_waybel_0(X1_62)
% 7.89/1.48      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1454,plain,
% 7.89/1.48      ( r1_waybel_0(X0_62,X1_62,sK2(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | m1_subset_1(k10_yellow_6(X0_62,X1_62),k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2097,plain,
% 7.89/1.48      ( r1_waybel_0(X0_62,X1_62,sK2(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_1454,c_1457]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10511,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X1_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_10492,c_2097]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2488,plain,
% 7.89/1.48      ( ~ l1_waybel_0(X0_62,X1_62)
% 7.89/1.48      | m1_subset_1(sK0(X1_62,X0_62,k1_xboole_0),u1_struct_0(X1_62))
% 7.89/1.48      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1_62)))
% 7.89/1.48      | ~ v2_pre_topc(X1_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ v4_orders_2(X0_62)
% 7.89/1.48      | ~ v7_waybel_0(X0_62)
% 7.89/1.48      | ~ l1_pre_topc(X1_62)
% 7.89/1.48      | k10_yellow_6(X1_62,X0_62) = k1_xboole_0 ),
% 7.89/1.48      inference(instantiation,[status(thm)],[c_504]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2493,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) = iProver_top
% 7.89/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0_62))) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_2488]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10516,plain,
% 7.89/1.48      ( r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X1_62)) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(global_propositional_subsumption,
% 7.89/1.48                [status(thm)],
% 7.89/1.48                [c_10511,c_2489,c_2493]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10517,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(sK0(X0_62,X1_62,k1_xboole_0),k10_yellow_6(X0_62,X1_62)) = iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(renaming,[status(thm)],[c_10516]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_23,plain,
% 7.89/1.48      ( r3_waybel_9(X0,X1,X2)
% 7.89/1.48      | ~ l1_waybel_0(X1,X0)
% 7.89/1.48      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 7.89/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.48      | ~ v2_pre_topc(X0)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | ~ v4_orders_2(X1)
% 7.89/1.48      | ~ v7_waybel_0(X1)
% 7.89/1.48      | ~ l1_pre_topc(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_489,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62)
% 7.89/1.48      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.48      | ~ r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62))
% 7.89/1.48      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.48      | ~ v2_pre_topc(X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ v4_orders_2(X1_62)
% 7.89/1.48      | ~ v7_waybel_0(X1_62)
% 7.89/1.48      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_23]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1468,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) != iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_2,plain,
% 7.89/1.48      ( ~ r2_hidden(X0,X1)
% 7.89/1.48      | m1_subset_1(X0,X2)
% 7.89/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.89/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_510,plain,
% 7.89/1.48      ( ~ r2_hidden(X0_62,X1_62)
% 7.89/1.48      | m1_subset_1(X0_62,X0_63)
% 7.89/1.48      | ~ m1_subset_1(X1_62,k1_zfmisc_1(X0_63)) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1447,plain,
% 7.89/1.48      ( r2_hidden(X0_62,X1_62) != iProver_top
% 7.89/1.48      | m1_subset_1(X0_62,X0_63) = iProver_top
% 7.89/1.48      | m1_subset_1(X1_62,k1_zfmisc_1(X0_63)) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_4006,plain,
% 7.89/1.48      ( l1_waybel_0(X0_62,X1_62) != iProver_top
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X1_62,X0_62)) != iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X1_62)) = iProver_top
% 7.89/1.48      | v2_pre_topc(X1_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X0_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X1_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_1457,c_1447]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_6001,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | r2_hidden(X2_62,k10_yellow_6(X0_62,X1_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_1468,c_4006]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10531,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r3_waybel_9(X0_62,X1_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_10517,c_6001]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_22,plain,
% 7.89/1.48      ( ~ r3_waybel_9(X0,X1,X2)
% 7.89/1.48      | r2_waybel_0(X0,X1,X3)
% 7.89/1.48      | ~ m1_connsp_2(X3,X0,X2)
% 7.89/1.48      | ~ l1_waybel_0(X1,X0)
% 7.89/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.48      | ~ v2_pre_topc(X0)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | ~ l1_pre_topc(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_490,plain,
% 7.89/1.48      ( ~ r3_waybel_9(X0_62,X1_62,X2_62)
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,X0_64)
% 7.89/1.48      | ~ m1_connsp_2(X0_64,X0_62,X2_62)
% 7.89/1.48      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.48      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.48      | ~ v2_pre_topc(X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_22]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1467,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
% 7.89/1.48      | m1_connsp_2(X0_64,X0_62,X2_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_10783,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
% 7.89/1.48      | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,k1_xboole_0)) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_10531,c_1467]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_13476,plain,
% 7.89/1.48      ( l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,k1_xboole_0)) != iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
% 7.89/1.48      | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(global_propositional_subsumption,
% 7.89/1.48                [status(thm)],
% 7.89/1.48                [c_10783,c_2489,c_2493]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_13477,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,X0_64) = iProver_top
% 7.89/1.48      | m1_connsp_2(X0_64,X0_62,sK0(X0_62,X1_62,k1_xboole_0)) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(renaming,[status(thm)],[c_13476]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_13492,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_1466,c_13477]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_13679,plain,
% 7.89/1.48      ( l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(global_propositional_subsumption,
% 7.89/1.48                [status(thm)],
% 7.89/1.48                [c_13492,c_2489,c_2493]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_13680,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(renaming,[status(thm)],[c_13679]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_17,plain,
% 7.89/1.48      ( ~ r2_waybel_0(X0,X1,X2)
% 7.89/1.48      | r2_waybel_0(X0,X3,X2)
% 7.89/1.48      | ~ m2_yellow_6(X1,X0,X3)
% 7.89/1.48      | ~ l1_waybel_0(X3,X0)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | v2_struct_0(X3)
% 7.89/1.48      | ~ v4_orders_2(X3)
% 7.89/1.48      | ~ v7_waybel_0(X3)
% 7.89/1.48      | ~ l1_struct_0(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_495,plain,
% 7.89/1.48      ( ~ r2_waybel_0(X0_62,X1_62,X0_64)
% 7.89/1.48      | r2_waybel_0(X0_62,X2_62,X0_64)
% 7.89/1.48      | ~ m2_yellow_6(X1_62,X0_62,X2_62)
% 7.89/1.48      | ~ l1_waybel_0(X2_62,X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X2_62)
% 7.89/1.48      | ~ v4_orders_2(X2_62)
% 7.89/1.48      | ~ v7_waybel_0(X2_62)
% 7.89/1.48      | ~ l1_struct_0(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_17]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1462,plain,
% 7.89/1.48      ( r2_waybel_0(X0_62,X1_62,X0_64) != iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X2_62,X0_64) = iProver_top
% 7.89/1.48      | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.48      | l1_struct_0(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_13695,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X3_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | m2_yellow_6(X1_62,X0_62,X3_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X3_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X3_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X3_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X3_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | l1_struct_0(X0_62) != iProver_top ),
% 7.89/1.48      inference(superposition,[status(thm)],[c_13680,c_1462]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_4,plain,
% 7.89/1.48      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_508,plain,
% 7.89/1.48      ( ~ l1_pre_topc(X0_62) | l1_struct_0(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_566,plain,
% 7.89/1.48      ( l1_pre_topc(X0_62) != iProver_top | l1_struct_0(X0_62) = iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_19230,plain,
% 7.89/1.48      ( l1_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X3_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X3_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X3_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X3_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m2_yellow_6(X1_62,X0_62,X3_62) != iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X3_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | k10_yellow_6(X0_62,X1_62) = k1_xboole_0 ),
% 7.89/1.48      inference(global_propositional_subsumption,[status(thm)],[c_13695,c_566]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_19231,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X3_62,sK3(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0))) = iProver_top
% 7.89/1.48      | m2_yellow_6(X1_62,X0_62,X3_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X3_62,X0_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X3_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.48      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.48      | v4_orders_2(X3_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.48      | v7_waybel_0(X3_62) != iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(renaming,[status(thm)],[c_19230]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_20,plain,
% 7.89/1.48      ( r3_waybel_9(X0,X1,X2)
% 7.89/1.48      | ~ r2_waybel_0(X0,X1,sK3(X0,X1,X2))
% 7.89/1.48      | ~ l1_waybel_0(X1,X0)
% 7.89/1.48      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.48      | ~ v2_pre_topc(X0)
% 7.89/1.48      | v2_struct_0(X0)
% 7.89/1.48      | v2_struct_0(X1)
% 7.89/1.48      | ~ l1_pre_topc(X0) ),
% 7.89/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_492,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62)
% 7.89/1.48      | ~ r2_waybel_0(X0_62,X1_62,sK3(X0_62,X1_62,X2_62))
% 7.89/1.48      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.48      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.48      | ~ v2_pre_topc(X0_62)
% 7.89/1.48      | v2_struct_0(X0_62)
% 7.89/1.48      | v2_struct_0(X1_62)
% 7.89/1.48      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.48      inference(subtyping,[status(esa)],[c_20]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_1465,plain,
% 7.89/1.48      ( r3_waybel_9(X0_62,X1_62,X2_62) = iProver_top
% 7.89/1.48      | r2_waybel_0(X0_62,X1_62,sK3(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.48      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.48      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.48      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.48      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.48      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.48      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 7.89/1.48  
% 7.89/1.48  cnf(c_19254,plain,
% 7.89/1.48      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.48      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.48      | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
% 7.89/1.48      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_19231,c_1465]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20191,plain,
% 7.89/1.49      ( l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
% 7.89/1.49      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.49      | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_19254,c_2489,c_2493]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20192,plain,
% 7.89/1.49      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.49      | r3_waybel_9(X0_62,X2_62,sK0(X0_62,X1_62,k1_xboole_0)) = iProver_top
% 7.89/1.49      | m2_yellow_6(X1_62,X0_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X2_62,X0_62) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_20191]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_33,plain,
% 7.89/1.49      ( ~ r3_waybel_9(X0,sK7(X0),X1)
% 7.89/1.49      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 7.89/1.49      | v1_compts_1(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_479,plain,
% 7.89/1.49      ( ~ r3_waybel_9(X0_62,sK7(X0_62),X1_62)
% 7.89/1.49      | ~ m1_subset_1(X1_62,u1_struct_0(X0_62))
% 7.89/1.49      | v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_33]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1478,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,sK7(X0_62),X1_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X1_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20211,plain,
% 7.89/1.49      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.49      | m2_yellow_6(X1_62,X0_62,sK7(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(X0_62),X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(sK0(X0_62,X1_62,k1_xboole_0),u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(X0_62)) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK7(X0_62)) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(X0_62)) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_20192,c_1478]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_35,plain,
% 7.89/1.49      ( l1_waybel_0(sK7(X0),X0)
% 7.89/1.49      | v1_compts_1(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f113]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_477,plain,
% 7.89/1.49      ( l1_waybel_0(sK7(X0_62),X0_62)
% 7.89/1.49      | v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_35]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_613,plain,
% 7.89/1.49      ( l1_waybel_0(sK7(X0_62),X0_62) = iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_36,plain,
% 7.89/1.49      ( v1_compts_1(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | v7_waybel_0(sK7(X0))
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f112]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_476,plain,
% 7.89/1.49      ( v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v7_waybel_0(sK7(X0_62))
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_36]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_614,plain,
% 7.89/1.49      ( v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(X0_62)) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_37,plain,
% 7.89/1.49      ( v1_compts_1(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | v4_orders_2(sK7(X0))
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_475,plain,
% 7.89/1.49      ( v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v4_orders_2(sK7(X0_62))
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_37]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_615,plain,
% 7.89/1.49      ( v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(X0_62)) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_38,plain,
% 7.89/1.49      ( v1_compts_1(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v2_struct_0(sK7(X0))
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_474,plain,
% 7.89/1.49      ( v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | ~ v2_struct_0(sK7(X0_62))
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_38]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_616,plain,
% 7.89/1.49      ( v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(X0_62)) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20585,plain,
% 7.89/1.49      ( v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m2_yellow_6(X1_62,X0_62,sK7(X0_62)) != iProver_top
% 7.89/1.49      | k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_20211,c_613,c_614,c_615,c_616,c_2489,c_2493]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20586,plain,
% 7.89/1.49      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.49      | m2_yellow_6(X1_62,X0_62,sK7(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_20585]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20601,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK11(sK7(sK9))) = k1_xboole_0
% 7.89/1.49      | l1_waybel_0(sK11(sK7(sK9)),sK9) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(sK9),sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK11(sK7(sK9))) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK11(sK7(sK9))) != iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK11(sK7(sK9))) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1492,c_20586]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_50,negated_conjecture,
% 7.89/1.49      ( ~ v2_struct_0(sK9) ),
% 7.89/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_51,plain,
% 7.89/1.49      ( v2_struct_0(sK9) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_49,negated_conjecture,
% 7.89/1.49      ( v2_pre_topc(sK9) ),
% 7.89/1.49      inference(cnf_transformation,[],[f117]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_52,plain,
% 7.89/1.49      ( v2_pre_topc(sK9) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_48,negated_conjecture,
% 7.89/1.49      ( l1_pre_topc(sK9) ),
% 7.89/1.49      inference(cnf_transformation,[],[f118]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_53,plain,
% 7.89/1.49      ( l1_pre_topc(sK9) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_73,plain,
% 7.89/1.49      ( v1_compts_1(X0) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0) != iProver_top
% 7.89/1.49      | v2_struct_0(X0) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(X0)) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_75,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) != iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_73]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_76,plain,
% 7.89/1.49      ( v1_compts_1(X0) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0) != iProver_top
% 7.89/1.49      | v2_struct_0(X0) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(X0)) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_78,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_76]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_79,plain,
% 7.89/1.49      ( v1_compts_1(X0) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0) != iProver_top
% 7.89/1.49      | v2_struct_0(X0) = iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(X0)) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_81,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_79]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_82,plain,
% 7.89/1.49      ( l1_waybel_0(sK7(X0),X0) = iProver_top
% 7.89/1.49      | v1_compts_1(X0) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0) != iProver_top
% 7.89/1.49      | v2_struct_0(X0) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_84,plain,
% 7.89/1.49      ( l1_waybel_0(sK7(sK9),sK9) = iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_82]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_165,plain,
% 7.89/1.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_167,plain,
% 7.89/1.49      ( l1_pre_topc(sK9) != iProver_top | l1_struct_0(sK9) = iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_165]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_46,negated_conjecture,
% 7.89/1.49      ( v3_yellow_6(sK11(X0),sK9)
% 7.89/1.49      | ~ l1_waybel_0(X0,sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v4_orders_2(X0)
% 7.89/1.49      | ~ v7_waybel_0(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f120]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_466,negated_conjecture,
% 7.89/1.49      ( v3_yellow_6(sK11(X0_62),sK9)
% 7.89/1.49      | ~ l1_waybel_0(X0_62,sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | ~ v7_waybel_0(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_46]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2672,plain,
% 7.89/1.49      ( v3_yellow_6(sK11(sK7(X0_62)),sK9)
% 7.89/1.49      | ~ l1_waybel_0(sK7(X0_62),sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(sK7(X0_62))
% 7.89/1.49      | ~ v4_orders_2(sK7(X0_62))
% 7.89/1.49      | ~ v7_waybel_0(sK7(X0_62)) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_466]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2693,plain,
% 7.89/1.49      ( v3_yellow_6(sK11(sK7(X0_62)),sK9) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(X0_62),sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(X0_62)) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(X0_62)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(X0_62)) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2672]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2695,plain,
% 7.89/1.49      ( v3_yellow_6(sK11(sK7(sK9)),sK9) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(sK9),sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2693]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2671,plain,
% 7.89/1.49      ( m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62))
% 7.89/1.49      | ~ l1_waybel_0(sK7(X0_62),sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(sK7(X0_62))
% 7.89/1.49      | ~ v4_orders_2(sK7(X0_62))
% 7.89/1.49      | ~ v7_waybel_0(sK7(X0_62)) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_465]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2697,plain,
% 7.89/1.49      ( m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62)) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(X0_62),sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(X0_62)) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(X0_62)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(X0_62)) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2671]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2699,plain,
% 7.89/1.49      ( m2_yellow_6(sK11(sK7(sK9)),sK9,sK7(sK9)) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(sK9),sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2697]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_19,plain,
% 7.89/1.49      ( ~ v3_yellow_6(X0,X1)
% 7.89/1.49      | ~ l1_waybel_0(X0,X1)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v4_orders_2(X0)
% 7.89/1.49      | ~ v7_waybel_0(X0)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | k10_yellow_6(X1,X0) != k1_xboole_0 ),
% 7.89/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_493,plain,
% 7.89/1.49      ( ~ v3_yellow_6(X0_62,X1_62)
% 7.89/1.49      | ~ l1_waybel_0(X0_62,X1_62)
% 7.89/1.49      | ~ v2_pre_topc(X1_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | ~ v7_waybel_0(X0_62)
% 7.89/1.49      | ~ l1_pre_topc(X1_62)
% 7.89/1.49      | k10_yellow_6(X1_62,X0_62) != k1_xboole_0 ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2954,plain,
% 7.89/1.49      ( ~ v3_yellow_6(sK11(sK7(X0_62)),sK9)
% 7.89/1.49      | ~ l1_waybel_0(sK11(sK7(X0_62)),sK9)
% 7.89/1.49      | ~ v2_pre_topc(sK9)
% 7.89/1.49      | v2_struct_0(sK11(sK7(X0_62)))
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | ~ v4_orders_2(sK11(sK7(X0_62)))
% 7.89/1.49      | ~ v7_waybel_0(sK11(sK7(X0_62)))
% 7.89/1.49      | ~ l1_pre_topc(sK9)
% 7.89/1.49      | k10_yellow_6(sK9,sK11(sK7(X0_62))) != k1_xboole_0 ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_493]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2960,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK11(sK7(X0_62))) != k1_xboole_0
% 7.89/1.49      | v3_yellow_6(sK11(sK7(X0_62)),sK9) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK11(sK7(X0_62)),sK9) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK11(sK7(X0_62))) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK11(sK7(X0_62))) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK11(sK7(X0_62))) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2954]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2962,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK11(sK7(sK9))) != k1_xboole_0
% 7.89/1.49      | v3_yellow_6(sK11(sK7(sK9)),sK9) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK11(sK7(sK9)),sK9) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK11(sK7(sK9))) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK11(sK7(sK9))) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK11(sK7(sK9))) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2960]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_13,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.89/1.49      | ~ l1_waybel_0(X2,X1)
% 7.89/1.49      | l1_waybel_0(X0,X1)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X2)
% 7.89/1.49      | ~ v4_orders_2(X2)
% 7.89/1.49      | ~ v7_waybel_0(X2)
% 7.89/1.49      | ~ l1_struct_0(X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_499,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
% 7.89/1.49      | ~ l1_waybel_0(X2_62,X1_62)
% 7.89/1.49      | l1_waybel_0(X0_62,X1_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | v2_struct_0(X2_62)
% 7.89/1.49      | ~ v4_orders_2(X2_62)
% 7.89/1.49      | ~ v7_waybel_0(X2_62)
% 7.89/1.49      | ~ l1_struct_0(X1_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2999,plain,
% 7.89/1.49      ( ~ m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62))
% 7.89/1.49      | l1_waybel_0(sK11(sK7(X0_62)),sK9)
% 7.89/1.49      | ~ l1_waybel_0(sK7(X0_62),sK9)
% 7.89/1.49      | v2_struct_0(sK7(X0_62))
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | ~ v4_orders_2(sK7(X0_62))
% 7.89/1.49      | ~ v7_waybel_0(sK7(X0_62))
% 7.89/1.49      | ~ l1_struct_0(sK9) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_499]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3010,plain,
% 7.89/1.49      ( m2_yellow_6(sK11(sK7(X0_62)),sK9,sK7(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK11(sK7(X0_62)),sK9) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(X0_62),sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK7(X0_62)) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(X0_62)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(X0_62)) != iProver_top
% 7.89/1.49      | l1_struct_0(sK9) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2999]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3012,plain,
% 7.89/1.49      ( m2_yellow_6(sK11(sK7(sK9)),sK9,sK7(sK9)) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK11(sK7(sK9)),sK9) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK7(sK9),sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) != iProver_top
% 7.89/1.49      | l1_struct_0(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_3010]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1480,plain,
% 7.89/1.49      ( l1_waybel_0(sK7(X0_62),X0_62) = iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_14,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.89/1.49      | ~ l1_waybel_0(X2,X1)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X2)
% 7.89/1.49      | ~ v4_orders_2(X2)
% 7.89/1.49      | ~ v7_waybel_0(X2)
% 7.89/1.49      | v7_waybel_0(X0)
% 7.89/1.49      | ~ l1_struct_0(X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_498,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
% 7.89/1.49      | ~ l1_waybel_0(X2_62,X1_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | v2_struct_0(X2_62)
% 7.89/1.49      | ~ v4_orders_2(X2_62)
% 7.89/1.49      | ~ v7_waybel_0(X2_62)
% 7.89/1.49      | v7_waybel_0(X0_62)
% 7.89/1.49      | ~ l1_struct_0(X1_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1459,plain,
% 7.89/1.49      ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X2_62,X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) = iProver_top
% 7.89/1.49      | l1_struct_0(X1_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3518,plain,
% 7.89/1.49      ( l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK11(X0_62)) = iProver_top
% 7.89/1.49      | l1_struct_0(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1492,c_1459]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3523,plain,
% 7.89/1.49      ( v7_waybel_0(sK11(X0_62)) = iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_3518,c_51,c_53,c_167]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3524,plain,
% 7.89/1.49      ( l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK11(X0_62)) = iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_3523]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3536,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK11(sK7(sK9))) = iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1480,c_3524]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3689,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v7_waybel_0(sK11(sK7(sK9))) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_3536,c_51,c_52,c_53,c_75,c_78,c_81]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_15,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.89/1.49      | ~ l1_waybel_0(X2,X1)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X2)
% 7.89/1.49      | ~ v4_orders_2(X2)
% 7.89/1.49      | v4_orders_2(X0)
% 7.89/1.49      | ~ v7_waybel_0(X2)
% 7.89/1.49      | ~ l1_struct_0(X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_497,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
% 7.89/1.49      | ~ l1_waybel_0(X2_62,X1_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | v2_struct_0(X2_62)
% 7.89/1.49      | ~ v4_orders_2(X2_62)
% 7.89/1.49      | v4_orders_2(X0_62)
% 7.89/1.49      | ~ v7_waybel_0(X2_62)
% 7.89/1.49      | ~ l1_struct_0(X1_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4218,plain,
% 7.89/1.49      ( ~ l1_waybel_0(X0_62,sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | v4_orders_2(sK11(X0_62))
% 7.89/1.49      | ~ v7_waybel_0(X0_62)
% 7.89/1.49      | ~ l1_struct_0(sK9) ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_497,c_465]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1460,plain,
% 7.89/1.49      ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X2_62,X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) = iProver_top
% 7.89/1.49      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.49      | l1_struct_0(X1_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3896,plain,
% 7.89/1.49      ( l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK11(X0_62)) = iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) != iProver_top
% 7.89/1.49      | l1_struct_0(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1492,c_1460]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4094,plain,
% 7.89/1.49      ( v7_waybel_0(X0_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK11(X0_62)) = iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_3896,c_51,c_53,c_167]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4095,plain,
% 7.89/1.49      ( l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK11(X0_62)) = iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_4094]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4096,plain,
% 7.89/1.49      ( ~ l1_waybel_0(X0_62,sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | v4_orders_2(sK11(X0_62))
% 7.89/1.49      | ~ v7_waybel_0(X0_62) ),
% 7.89/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4095]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4221,plain,
% 7.89/1.49      ( ~ v7_waybel_0(X0_62)
% 7.89/1.49      | v4_orders_2(sK11(X0_62))
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | ~ l1_waybel_0(X0_62,sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(X0_62) ),
% 7.89/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4218,c_4096]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4222,plain,
% 7.89/1.49      ( ~ l1_waybel_0(X0_62,sK9)
% 7.89/1.49      | v1_compts_1(sK9)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | v4_orders_2(sK11(X0_62))
% 7.89/1.49      | ~ v7_waybel_0(X0_62) ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_4221]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4253,plain,
% 7.89/1.49      ( v1_compts_1(sK9)
% 7.89/1.49      | ~ v2_pre_topc(sK9)
% 7.89/1.49      | v2_struct_0(sK7(sK9))
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | v4_orders_2(sK11(sK7(sK9)))
% 7.89/1.49      | ~ v4_orders_2(sK7(sK9))
% 7.89/1.49      | ~ v7_waybel_0(sK7(sK9))
% 7.89/1.49      | ~ l1_pre_topc(sK9) ),
% 7.89/1.49      inference(resolution,[status(thm)],[c_4222,c_477]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_74,plain,
% 7.89/1.49      ( v1_compts_1(sK9)
% 7.89/1.49      | ~ v2_pre_topc(sK9)
% 7.89/1.49      | ~ v2_struct_0(sK7(sK9))
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | ~ l1_pre_topc(sK9) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_38]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_77,plain,
% 7.89/1.49      ( v1_compts_1(sK9)
% 7.89/1.49      | ~ v2_pre_topc(sK9)
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | v4_orders_2(sK7(sK9))
% 7.89/1.49      | ~ l1_pre_topc(sK9) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_37]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_80,plain,
% 7.89/1.49      ( v1_compts_1(sK9)
% 7.89/1.49      | ~ v2_pre_topc(sK9)
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | v7_waybel_0(sK7(sK9))
% 7.89/1.49      | ~ l1_pre_topc(sK9) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_36]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4107,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK11(sK7(sK9))) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1480,c_4095]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4141,plain,
% 7.89/1.49      ( v1_compts_1(sK9)
% 7.89/1.49      | ~ v2_pre_topc(sK9)
% 7.89/1.49      | v2_struct_0(sK7(sK9))
% 7.89/1.49      | v2_struct_0(sK9)
% 7.89/1.49      | v4_orders_2(sK11(sK7(sK9)))
% 7.89/1.49      | ~ v4_orders_2(sK7(sK9))
% 7.89/1.49      | ~ v7_waybel_0(sK7(sK9))
% 7.89/1.49      | ~ l1_pre_topc(sK9) ),
% 7.89/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4107]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4561,plain,
% 7.89/1.49      ( v4_orders_2(sK11(sK7(sK9))) | v1_compts_1(sK9) ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_4253,c_50,c_49,c_48,c_74,c_77,c_80,c_4141]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4562,plain,
% 7.89/1.49      ( v1_compts_1(sK9) | v4_orders_2(sK11(sK7(sK9))) ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_4561]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4563,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK11(sK7(sK9))) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_4562]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_16,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0,X1,X2)
% 7.89/1.49      | ~ l1_waybel_0(X2,X1)
% 7.89/1.49      | ~ v2_struct_0(X0)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X2)
% 7.89/1.49      | ~ v4_orders_2(X2)
% 7.89/1.49      | ~ v7_waybel_0(X2)
% 7.89/1.49      | ~ l1_struct_0(X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_496,plain,
% 7.89/1.49      ( ~ m2_yellow_6(X0_62,X1_62,X2_62)
% 7.89/1.49      | ~ l1_waybel_0(X2_62,X1_62)
% 7.89/1.49      | ~ v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | v2_struct_0(X2_62)
% 7.89/1.49      | ~ v4_orders_2(X2_62)
% 7.89/1.49      | ~ v7_waybel_0(X2_62)
% 7.89/1.49      | ~ l1_struct_0(X1_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1461,plain,
% 7.89/1.49      ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X2_62,X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.49      | l1_struct_0(X1_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_3993,plain,
% 7.89/1.49      ( l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK11(X0_62)) != iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) != iProver_top
% 7.89/1.49      | l1_struct_0(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1492,c_1461]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4482,plain,
% 7.89/1.49      ( v7_waybel_0(X0_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK11(X0_62)) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_3993,c_51,c_53,c_167]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4483,plain,
% 7.89/1.49      ( l1_waybel_0(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK11(X0_62)) != iProver_top
% 7.89/1.49      | v4_orders_2(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_4482]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4495,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK11(sK7(sK9))) != iProver_top
% 7.89/1.49      | v2_struct_0(sK7(sK9)) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK7(sK9)) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK7(sK9)) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1480,c_4483]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4711,plain,
% 7.89/1.49      ( v2_struct_0(sK11(sK7(sK9))) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_4495,c_51,c_52,c_53,c_75,c_78,c_81]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_4712,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top
% 7.89/1.49      | v2_struct_0(sK11(sK7(sK9))) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_4711]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20646,plain,
% 7.89/1.49      ( v1_compts_1(sK9) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_20601,c_51,c_52,c_53,c_75,c_78,c_81,c_84,c_167,c_2695,
% 7.89/1.49                 c_2699,c_2962,c_3012,c_3689,c_4563,c_4712]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_31,plain,
% 7.89/1.49      ( r3_waybel_9(X0,X1,sK6(X0,X1))
% 7.89/1.49      | ~ l1_waybel_0(X1,X0)
% 7.89/1.49      | ~ v1_compts_1(X0)
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | ~ v4_orders_2(X1)
% 7.89/1.49      | ~ v7_waybel_0(X1)
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_481,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,sK6(X0_62,X1_62))
% 7.89/1.49      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.49      | ~ v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | ~ v4_orders_2(X1_62)
% 7.89/1.49      | ~ v7_waybel_0(X1_62)
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_31]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1476,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,sK6(X0_62,X1_62)) = iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_25,plain,
% 7.89/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.89/1.49      | m2_yellow_6(sK4(X0,X1,X2),X0,X1)
% 7.89/1.49      | ~ l1_waybel_0(X1,X0)
% 7.89/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | ~ v4_orders_2(X1)
% 7.89/1.49      | ~ v7_waybel_0(X1)
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_487,plain,
% 7.89/1.49      ( ~ r3_waybel_9(X0_62,X1_62,X2_62)
% 7.89/1.49      | m2_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62,X1_62)
% 7.89/1.49      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.49      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | ~ v4_orders_2(X1_62)
% 7.89/1.49      | ~ v7_waybel_0(X1_62)
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1470,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | m2_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62,X1_62) = iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1458,plain,
% 7.89/1.49      ( m2_yellow_6(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X2_62,X1_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X0_62,X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X2_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X2_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X2_62) != iProver_top
% 7.89/1.49      | l1_struct_0(X1_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6131,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | l1_struct_0(X0_62) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1470,c_1458]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7022,plain,
% 7.89/1.49      ( l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6131,c_566]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7023,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_7022]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_18,plain,
% 7.89/1.49      ( v3_yellow_6(X0,X1)
% 7.89/1.49      | ~ l1_waybel_0(X0,X1)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v4_orders_2(X0)
% 7.89/1.49      | ~ v7_waybel_0(X0)
% 7.89/1.49      | ~ l1_pre_topc(X1)
% 7.89/1.49      | k10_yellow_6(X1,X0) = k1_xboole_0 ),
% 7.89/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_494,plain,
% 7.89/1.49      ( v3_yellow_6(X0_62,X1_62)
% 7.89/1.49      | ~ l1_waybel_0(X0_62,X1_62)
% 7.89/1.49      | ~ v2_pre_topc(X1_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | ~ v7_waybel_0(X0_62)
% 7.89/1.49      | ~ l1_pre_topc(X1_62)
% 7.89/1.49      | k10_yellow_6(X1_62,X0_62) = k1_xboole_0 ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1463,plain,
% 7.89/1.49      ( k10_yellow_6(X0_62,X1_62) = k1_xboole_0
% 7.89/1.49      | v3_yellow_6(X1_62,X0_62) = iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_7041,plain,
% 7.89/1.49      ( k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)) = k1_xboole_0
% 7.89/1.49      | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | v3_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK4(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_7023,c_1463]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6132,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK4(X0_62,X1_62,X2_62)) = iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | l1_struct_0(X0_62) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1470,c_1460]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6851,plain,
% 7.89/1.49      ( l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK4(X0_62,X1_62,X2_62)) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6132,c_566]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6852,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(sK4(X0_62,X1_62,X2_62)) = iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_6851]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6133,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | l1_struct_0(X0_62) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1470,c_1459]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6935,plain,
% 7.89/1.49      ( l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6133,c_566]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6936,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK4(X0_62,X1_62,X2_62)) = iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_6935]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6130,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | l1_struct_0(X0_62) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1470,c_1461]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6952,plain,
% 7.89/1.49      ( l1_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,[status(thm)],[c_6130,c_566]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6953,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK4(X0_62,X1_62,X2_62)) != iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_6952]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8450,plain,
% 7.89/1.49      ( v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | v3_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
% 7.89/1.49      | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)) = k1_xboole_0
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_7041,c_6852,c_6936,c_6953]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8451,plain,
% 7.89/1.49      ( k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)) = k1_xboole_0
% 7.89/1.49      | r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | v3_yellow_6(sK4(X0_62,X1_62,X2_62),X0_62) = iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_8450]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_41,negated_conjecture,
% 7.89/1.49      ( ~ m2_yellow_6(X0,sK9,sK10)
% 7.89/1.49      | ~ v3_yellow_6(X0,sK9)
% 7.89/1.49      | ~ v1_compts_1(sK9) ),
% 7.89/1.49      inference(cnf_transformation,[],[f125]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_471,negated_conjecture,
% 7.89/1.49      ( ~ m2_yellow_6(X0_62,sK9,sK10)
% 7.89/1.49      | ~ v3_yellow_6(X0_62,sK9)
% 7.89/1.49      | ~ v1_compts_1(sK9) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_41]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1486,plain,
% 7.89/1.49      ( m2_yellow_6(X0_62,sK9,sK10) != iProver_top
% 7.89/1.49      | v3_yellow_6(X0_62,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6129,plain,
% 7.89/1.49      ( r3_waybel_9(sK9,sK10,X0_62) != iProver_top
% 7.89/1.49      | v3_yellow_6(sK4(sK9,sK10,X0_62),sK9) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK10,sK9) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1470,c_1486]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_45,negated_conjecture,
% 7.89/1.49      ( ~ v1_compts_1(sK9) | ~ v2_struct_0(sK10) ),
% 7.89/1.49      inference(cnf_transformation,[],[f121]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_60,plain,
% 7.89/1.49      ( v1_compts_1(sK9) != iProver_top | v2_struct_0(sK10) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_44,negated_conjecture,
% 7.89/1.49      ( ~ v1_compts_1(sK9) | v4_orders_2(sK10) ),
% 7.89/1.49      inference(cnf_transformation,[],[f122]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_61,plain,
% 7.89/1.49      ( v1_compts_1(sK9) != iProver_top | v4_orders_2(sK10) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_43,negated_conjecture,
% 7.89/1.49      ( ~ v1_compts_1(sK9) | v7_waybel_0(sK10) ),
% 7.89/1.49      inference(cnf_transformation,[],[f123]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_62,plain,
% 7.89/1.49      ( v1_compts_1(sK9) != iProver_top | v7_waybel_0(sK10) = iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_42,negated_conjecture,
% 7.89/1.49      ( l1_waybel_0(sK10,sK9) | ~ v1_compts_1(sK9) ),
% 7.89/1.49      inference(cnf_transformation,[],[f124]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_63,plain,
% 7.89/1.49      ( l1_waybel_0(sK10,sK9) = iProver_top | v1_compts_1(sK9) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6524,plain,
% 7.89/1.49      ( v3_yellow_6(sK4(sK9,sK10,X0_62),sK9) != iProver_top
% 7.89/1.49      | r3_waybel_9(sK9,sK10,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_6129,c_51,c_52,c_53,c_60,c_61,c_62,c_63]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_6525,plain,
% 7.89/1.49      ( r3_waybel_9(sK9,sK10,X0_62) != iProver_top
% 7.89/1.49      | v3_yellow_6(sK4(sK9,sK10,X0_62),sK9) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_6524]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_8467,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK4(sK9,sK10,X0_62)) = k1_xboole_0
% 7.89/1.49      | r3_waybel_9(sK9,sK10,X0_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK10,sK9) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_8451,c_6525]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_9138,plain,
% 7.89/1.49      ( r3_waybel_9(sK9,sK10,X0_62) != iProver_top
% 7.89/1.49      | k10_yellow_6(sK9,sK4(sK9,sK10,X0_62)) = k1_xboole_0
% 7.89/1.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_8467,c_51,c_52,c_53,c_60,c_61,c_62,c_63]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_9139,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK4(sK9,sK10,X0_62)) = k1_xboole_0
% 7.89/1.49      | r3_waybel_9(sK9,sK10,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(X0_62,u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top ),
% 7.89/1.49      inference(renaming,[status(thm)],[c_9138]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_9149,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK4(sK9,sK10,sK6(sK9,sK10))) = k1_xboole_0
% 7.89/1.49      | l1_waybel_0(sK10,sK9) != iProver_top
% 7.89/1.49      | m1_subset_1(sK6(sK9,sK10),u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_1476,c_9139]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_32,plain,
% 7.89/1.49      ( ~ l1_waybel_0(X0,X1)
% 7.89/1.49      | m1_subset_1(sK6(X1,X0),u1_struct_0(X1))
% 7.89/1.49      | ~ v1_compts_1(X1)
% 7.89/1.49      | ~ v2_pre_topc(X1)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | ~ v4_orders_2(X0)
% 7.89/1.49      | ~ v7_waybel_0(X0)
% 7.89/1.49      | ~ l1_pre_topc(X1) ),
% 7.89/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_480,plain,
% 7.89/1.49      ( ~ l1_waybel_0(X0_62,X1_62)
% 7.89/1.49      | m1_subset_1(sK6(X1_62,X0_62),u1_struct_0(X1_62))
% 7.89/1.49      | ~ v1_compts_1(X1_62)
% 7.89/1.49      | ~ v2_pre_topc(X1_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | ~ v4_orders_2(X0_62)
% 7.89/1.49      | ~ v7_waybel_0(X0_62)
% 7.89/1.49      | ~ l1_pre_topc(X1_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_32]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2398,plain,
% 7.89/1.49      ( ~ l1_waybel_0(sK10,X0_62)
% 7.89/1.49      | m1_subset_1(sK6(X0_62,sK10),u1_struct_0(X0_62))
% 7.89/1.49      | ~ v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(sK10)
% 7.89/1.49      | ~ v4_orders_2(sK10)
% 7.89/1.49      | ~ v7_waybel_0(sK10)
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_480]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2399,plain,
% 7.89/1.49      ( l1_waybel_0(sK10,X0_62) != iProver_top
% 7.89/1.49      | m1_subset_1(sK6(X0_62,sK10),u1_struct_0(X0_62)) = iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2401,plain,
% 7.89/1.49      ( l1_waybel_0(sK10,sK9) != iProver_top
% 7.89/1.49      | m1_subset_1(sK6(sK9,sK10),u1_struct_0(sK9)) = iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2399]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_9361,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK4(sK9,sK10,sK6(sK9,sK10))) = k1_xboole_0
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_9149,c_51,c_52,c_53,c_60,c_61,c_62,c_63,c_2401]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_20654,plain,
% 7.89/1.49      ( k10_yellow_6(sK9,sK4(sK9,sK10,sK6(sK9,sK10))) = k1_xboole_0 ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_20646,c_9361]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_24,plain,
% 7.89/1.49      ( ~ r3_waybel_9(X0,X1,X2)
% 7.89/1.49      | ~ l1_waybel_0(X1,X0)
% 7.89/1.49      | r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
% 7.89/1.49      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 7.89/1.49      | ~ v2_pre_topc(X0)
% 7.89/1.49      | v2_struct_0(X0)
% 7.89/1.49      | v2_struct_0(X1)
% 7.89/1.49      | ~ v4_orders_2(X1)
% 7.89/1.49      | ~ v7_waybel_0(X1)
% 7.89/1.49      | ~ l1_pre_topc(X0) ),
% 7.89/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_488,plain,
% 7.89/1.49      ( ~ r3_waybel_9(X0_62,X1_62,X2_62)
% 7.89/1.49      | ~ l1_waybel_0(X1_62,X0_62)
% 7.89/1.49      | r2_hidden(X2_62,k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62)))
% 7.89/1.49      | ~ m1_subset_1(X2_62,u1_struct_0(X0_62))
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(X1_62)
% 7.89/1.49      | ~ v4_orders_2(X1_62)
% 7.89/1.49      | ~ v7_waybel_0(X1_62)
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(subtyping,[status(esa)],[c_24]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_1469,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,X1_62,X2_62) != iProver_top
% 7.89/1.49      | l1_waybel_0(X1_62,X0_62) != iProver_top
% 7.89/1.49      | r2_hidden(X2_62,k10_yellow_6(X0_62,sK4(X0_62,X1_62,X2_62))) = iProver_top
% 7.89/1.49      | m1_subset_1(X2_62,u1_struct_0(X0_62)) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(X1_62) = iProver_top
% 7.89/1.49      | v4_orders_2(X1_62) != iProver_top
% 7.89/1.49      | v7_waybel_0(X1_62) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_21502,plain,
% 7.89/1.49      ( r3_waybel_9(sK9,sK10,sK6(sK9,sK10)) != iProver_top
% 7.89/1.49      | l1_waybel_0(sK10,sK9) != iProver_top
% 7.89/1.49      | r2_hidden(sK6(sK9,sK10),k1_xboole_0) = iProver_top
% 7.89/1.49      | m1_subset_1(sK6(sK9,sK10),u1_struct_0(sK9)) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_20654,c_1469]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2439,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,sK10,sK6(X0_62,sK10))
% 7.89/1.49      | ~ l1_waybel_0(sK10,X0_62)
% 7.89/1.49      | ~ v1_compts_1(X0_62)
% 7.89/1.49      | ~ v2_pre_topc(X0_62)
% 7.89/1.49      | v2_struct_0(X0_62)
% 7.89/1.49      | v2_struct_0(sK10)
% 7.89/1.49      | ~ v4_orders_2(sK10)
% 7.89/1.49      | ~ v7_waybel_0(sK10)
% 7.89/1.49      | ~ l1_pre_topc(X0_62) ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_481]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2440,plain,
% 7.89/1.49      ( r3_waybel_9(X0_62,sK10,sK6(X0_62,sK10)) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK10,X0_62) != iProver_top
% 7.89/1.49      | v1_compts_1(X0_62) != iProver_top
% 7.89/1.49      | v2_pre_topc(X0_62) != iProver_top
% 7.89/1.49      | v2_struct_0(X0_62) = iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(X0_62) != iProver_top ),
% 7.89/1.49      inference(predicate_to_equality,[status(thm)],[c_2439]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_2442,plain,
% 7.89/1.49      ( r3_waybel_9(sK9,sK10,sK6(sK9,sK10)) = iProver_top
% 7.89/1.49      | l1_waybel_0(sK10,sK9) != iProver_top
% 7.89/1.49      | v1_compts_1(sK9) != iProver_top
% 7.89/1.49      | v2_pre_topc(sK9) != iProver_top
% 7.89/1.49      | v2_struct_0(sK10) = iProver_top
% 7.89/1.49      | v2_struct_0(sK9) = iProver_top
% 7.89/1.49      | v4_orders_2(sK10) != iProver_top
% 7.89/1.49      | v7_waybel_0(sK10) != iProver_top
% 7.89/1.49      | l1_pre_topc(sK9) != iProver_top ),
% 7.89/1.49      inference(instantiation,[status(thm)],[c_2440]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_22996,plain,
% 7.89/1.49      ( r2_hidden(sK6(sK9,sK10),k1_xboole_0) = iProver_top ),
% 7.89/1.49      inference(global_propositional_subsumption,
% 7.89/1.49                [status(thm)],
% 7.89/1.49                [c_21502,c_51,c_52,c_53,c_60,c_61,c_62,c_63,c_75,c_78,c_81,
% 7.89/1.49                 c_84,c_167,c_2401,c_2442,c_2695,c_2699,c_2962,c_3012,c_3689,
% 7.89/1.49                 c_4563,c_4712,c_20601]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_23001,plain,
% 7.89/1.49      ( r1_tarski(k1_xboole_0,sK6(sK9,sK10)) != iProver_top ),
% 7.89/1.49      inference(superposition,[status(thm)],[c_22996,c_1448]) ).
% 7.89/1.49  
% 7.89/1.49  cnf(c_23866,plain,
% 7.89/1.49      ( $false ),
% 7.89/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_23001,c_1445]) ).
% 7.89/1.49  
% 7.89/1.49  
% 7.89/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.89/1.49  
% 7.89/1.49  ------                               Statistics
% 7.89/1.49  
% 7.89/1.49  ------ Selected
% 7.89/1.49  
% 7.89/1.49  total_time:                             0.902
% 7.89/1.49  
%------------------------------------------------------------------------------
