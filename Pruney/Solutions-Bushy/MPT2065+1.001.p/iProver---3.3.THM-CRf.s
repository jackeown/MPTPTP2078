%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2065+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:07 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  170 (1468 expanded)
%              Number of clauses        :  103 ( 251 expanded)
%              Number of leaves         :   14 ( 444 expanded)
%              Depth                    :   25
%              Number of atoms          :  989 (22291 expanded)
%              Number of equality atoms :  115 ( 212 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   44 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X3] :
                      ( r3_waybel_9(X0,X3,X2)
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ? [X4] :
                      ( r3_waybel_9(X0,X4,X2)
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK1(X0,X1,X2),X1)
        & l1_waybel_0(sK1(X0,X1,X2),X0)
        & v7_waybel_0(sK1(X0,X1,X2))
        & v4_orders_2(sK1(X0,X1,X2))
        & ~ v2_struct_0(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ! [X3] :
                      ( ~ r3_waybel_9(X0,X3,X2)
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) ) )
                & ( ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK1(X0,X1,X2),X1)
                    & l1_waybel_0(sK1(X0,X1,X2),X0)
                    & v7_waybel_0(sK1(X0,X1,X2))
                    & v4_orders_2(sK1(X0,X1,X2))
                    & ~ v2_struct_0(sK1(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r3_waybel_9(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( l1_waybel_0(X2,X0)
                    & v7_waybel_0(X2)
                    & v4_orders_2(X2)
                    & ~ v2_struct_0(X2) )
                 => ( r1_waybel_0(X0,X2,X1)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r3_waybel_9(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_waybel_0(X0,X2,X1)
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_waybel_0(X0,X2,X1)
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_waybel_0(X0,X2,X1)
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r3_waybel_9(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X4,X1)
                | ~ l1_waybel_0(X4,X0)
                | ~ v7_waybel_0(X4)
                | ~ v4_orders_2(X4)
                | v2_struct_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r3_waybel_9(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5,X1)
        & r3_waybel_9(X0,X2,sK5)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r3_waybel_9(X0,X2,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r3_waybel_9(X0,sK4,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_waybel_0(X0,sK4,X1)
        & l1_waybel_0(sK4,X0)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r3_waybel_9(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_waybel_0(X0,X2,X1)
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r3_waybel_9(X0,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X4,X1)
                | ~ l1_waybel_0(X4,X0)
                | ~ v7_waybel_0(X4)
                | ~ v4_orders_2(X4)
                | v2_struct_0(X4) )
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X3,sK3)
                  & r3_waybel_9(X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_waybel_0(X0,X2,sK3)
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          | ~ v4_pre_topc(sK3,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,sK3)
                  | ~ r3_waybel_9(X0,X4,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ r1_waybel_0(X0,X4,sK3)
              | ~ l1_waybel_0(X4,X0)
              | ~ v7_waybel_0(X4)
              | ~ v4_orders_2(X4)
              | v2_struct_0(X4) )
          | v4_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r3_waybel_9(X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_waybel_0(X0,X2,X1)
                  & l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
              | ~ v4_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r3_waybel_9(X0,X4,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r1_waybel_0(X0,X4,X1)
                  | ~ l1_waybel_0(X4,X0)
                  | ~ v7_waybel_0(X4)
                  | ~ v4_orders_2(X4)
                  | v2_struct_0(X4) )
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X3,X1)
                    & r3_waybel_9(sK2,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK2)) )
                & r1_waybel_0(sK2,X2,X1)
                & l1_waybel_0(X2,sK2)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            | ~ v4_pre_topc(X1,sK2) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X1)
                    | ~ r3_waybel_9(sK2,X4,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                | ~ r1_waybel_0(sK2,X4,X1)
                | ~ l1_waybel_0(X4,sK2)
                | ~ v7_waybel_0(X4)
                | ~ v4_orders_2(X4)
                | v2_struct_0(X4) )
            | v4_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( ( ~ r2_hidden(sK5,sK3)
        & r3_waybel_9(sK2,sK4,sK5)
        & m1_subset_1(sK5,u1_struct_0(sK2))
        & r1_waybel_0(sK2,sK4,sK3)
        & l1_waybel_0(sK4,sK2)
        & v7_waybel_0(sK4)
        & v4_orders_2(sK4)
        & ~ v2_struct_0(sK4) )
      | ~ v4_pre_topc(sK3,sK2) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,sK3)
              | ~ r3_waybel_9(sK2,X4,X5)
              | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
          | ~ r1_waybel_0(sK2,X4,sK3)
          | ~ l1_waybel_0(X4,sK2)
          | ~ v7_waybel_0(X4)
          | ~ v4_orders_2(X4)
          | v2_struct_0(X4) )
      | v4_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f36,f40,f39,f38,f37])).

fof(f63,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,sK3)
      | ~ r3_waybel_9(sK2,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK2))
      | ~ r1_waybel_0(sK2,X4,sK3)
      | ~ l1_waybel_0(X4,sK2)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | v4_pre_topc(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK1(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,
    ( r3_waybel_9(sK2,sK4,sK5)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r3_waybel_9(X0,X3,X2)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ l1_waybel_0(X3,X0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,
    ( ~ v2_struct_0(sK4)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,
    ( v4_orders_2(sK4)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,
    ( v7_waybel_0(sK4)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,
    ( l1_waybel_0(sK4,sK2)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f72,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,
    ( r1_waybel_0(sK2,sK4,sK3)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2324,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9,plain,
    ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_458,plain,
    ( r1_waybel_0(X0,sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_459,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_463,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_32,c_30])).

cnf(c_2315,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0,X1),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_28,negated_conjecture,
    ( ~ r1_waybel_0(sK2,X0,sK3)
    | ~ r3_waybel_9(sK2,X0,X1)
    | v4_pre_topc(sK3,sK2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_8,plain,
    ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_482,plain,
    ( r3_waybel_9(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_31])).

cnf(c_483,plain,
    ( r3_waybel_9(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( r3_waybel_9(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_32,c_30])).

cnf(c_757,plain,
    ( ~ r1_waybel_0(sK2,X0,sK3)
    | v4_pre_topc(sK3,sK2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ m1_subset_1(X3,u1_struct_0(sK2))
    | ~ r2_hidden(X3,k2_pre_topc(sK2,X1))
    | r2_hidden(X2,sK3)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | X3 != X2
    | sK1(sK2,X1,X3) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_487])).

cnf(c_758,plain,
    ( ~ r1_waybel_0(sK2,sK1(sK2,X0,X1),sK3)
    | v4_pre_topc(sK3,sK2)
    | ~ l1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | r2_hidden(X1,sK3)
    | v2_struct_0(sK1(sK2,X0,X1))
    | ~ v4_orders_2(sK1(sK2,X0,X1))
    | ~ v7_waybel_0(sK1(sK2,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_10,plain,
    ( l1_waybel_0(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_434,plain,
    ( l1_waybel_0(sK1(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_435,plain,
    ( l1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_439,plain,
    ( l1_waybel_0(sK1(sK2,X0,X1),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_32,c_30])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_567,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ v2_struct_0(sK1(sK2,X0,X1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_566])).

cnf(c_571,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ v2_struct_0(sK1(sK2,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_567,c_32,c_30])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v4_orders_2(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | v4_orders_2(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_31])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | v4_orders_2(sK1(sK2,X0,X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_595,plain,
    ( v4_orders_2(sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_32,c_30])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v4_orders_2(sK1(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_595])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,X0))
    | v2_struct_0(X1)
    | v7_waybel_0(sK1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK2)
    | v7_waybel_0(sK1(sK2,X0,X1))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_619,plain,
    ( v7_waybel_0(sK1(sK2,X0,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_615,c_32,c_30])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | v7_waybel_0(sK1(sK2,X0,X1)) ),
    inference(renaming,[status(thm)],[c_619])).

cnf(c_762,plain,
    ( r2_hidden(X1,sK3)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_waybel_0(sK2,sK1(sK2,X0,X1),sK3)
    | v4_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_32,c_30,c_439,c_567,c_596,c_620])).

cnf(c_763,plain,
    ( ~ r1_waybel_0(sK2,sK1(sK2,X0,X1),sK3)
    | v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | r2_hidden(X1,sK3) ),
    inference(renaming,[status(thm)],[c_762])).

cnf(c_2309,plain,
    ( r1_waybel_0(sK2,sK1(sK2,X0,X1),sK3) != iProver_top
    | v4_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top
    | r2_hidden(X1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_3151,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2315,c_2309])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2316,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_709,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_2311,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2320,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3249,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X1,k2_pre_topc(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_2320])).

cnf(c_3863,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_3249])).

cnf(c_4636,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top
    | r2_hidden(X0,k2_pre_topc(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3151,c_36,c_3863])).

cnf(c_4645,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top
    | r2_hidden(sK0(k2_pre_topc(sK2,sK3),X0),sK3) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_4636])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2325,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5469,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top
    | r1_tarski(k2_pre_topc(sK2,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4645,c_2325])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_697,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_698,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,k2_pre_topc(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_2486,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_2487,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2486])).

cnf(c_18,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_545,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_31])).

cnf(c_546,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(X0,sK2)
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_30])).

cnf(c_551,plain,
    ( v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != X0 ),
    inference(renaming,[status(thm)],[c_550])).

cnf(c_2489,plain,
    ( v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_551])).

cnf(c_2490,plain,
    ( k2_pre_topc(sK2,sK3) != sK3
    | v4_pre_topc(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2489])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2531,plain,
    ( ~ r1_tarski(k2_pre_topc(sK2,sK3),sK3)
    | ~ r1_tarski(sK3,k2_pre_topc(sK2,sK3))
    | k2_pre_topc(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2532,plain,
    ( k2_pre_topc(sK2,sK3) = sK3
    | r1_tarski(k2_pre_topc(sK2,sK3),sK3) != iProver_top
    | r1_tarski(sK3,k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2531])).

cnf(c_5500,plain,
    ( v4_pre_topc(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5469,c_36,c_2487,c_2490,c_2532])).

cnf(c_19,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_682,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_683,plain,
    ( ~ v4_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_2313,plain,
    ( k2_pre_topc(sK2,X0) = X0
    | v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_2593,plain,
    ( k2_pre_topc(sK2,sK3) = sK3
    | v4_pre_topc(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2313])).

cnf(c_5505,plain,
    ( k2_pre_topc(sK2,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_5500,c_2593])).

cnf(c_21,negated_conjecture,
    ( r3_waybel_9(sK2,sK4,sK5)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r3_waybel_9(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(X3,k2_pre_topc(X0,X2))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_506,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | ~ r3_waybel_9(X0,X1,X3)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | r2_hidden(X3,k2_pre_topc(X0,X2))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_31])).

cnf(c_507,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | ~ r3_waybel_9(sK2,X0,X2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | r2_hidden(X2,k2_pre_topc(sK2,X1))
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_511,plain,
    ( ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | ~ r1_waybel_0(sK2,X0,X1)
    | ~ r3_waybel_9(sK2,X0,X2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | r2_hidden(X2,k2_pre_topc(sK2,X1))
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_32,c_30])).

cnf(c_512,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | ~ r3_waybel_9(sK2,X0,X2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | r2_hidden(X2,k2_pre_topc(sK2,X1))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_733,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | ~ v4_pre_topc(sK3,sK2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | r2_hidden(X2,k2_pre_topc(sK2,X1))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | sK4 != X0
    | sK2 != sK2
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_512])).

cnf(c_734,plain,
    ( ~ r1_waybel_0(sK2,sK4,X0)
    | ~ v4_pre_topc(sK3,sK2)
    | ~ l1_waybel_0(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r2_hidden(sK5,k2_pre_topc(sK2,X0))
    | v2_struct_0(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v7_waybel_0(sK4) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_27,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | v7_waybel_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | l1_waybel_0(sK4,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_22,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_738,plain,
    ( r2_hidden(sK5,k2_pre_topc(sK2,X0))
    | ~ v4_pre_topc(sK3,sK2)
    | ~ r1_waybel_0(sK2,sK4,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_27,c_26,c_25,c_24,c_22])).

cnf(c_739,plain,
    ( ~ r1_waybel_0(sK2,sK4,X0)
    | ~ v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,k2_pre_topc(sK2,X0)) ),
    inference(renaming,[status(thm)],[c_738])).

cnf(c_2310,plain,
    ( r1_waybel_0(sK2,sK4,X0) != iProver_top
    | v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_3012,plain,
    ( r1_waybel_0(sK2,sK4,sK3) != iProver_top
    | v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_2310])).

cnf(c_23,negated_conjecture,
    ( r1_waybel_0(sK2,sK4,sK3)
    | ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_832,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,k2_pre_topc(sK2,X0))
    | sK4 != sK4
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_739])).

cnf(c_833,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_832])).

cnf(c_834,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_3044,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3012,c_36,c_834])).

cnf(c_5645,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5505,c_3044])).

cnf(c_20,negated_conjecture,
    ( ~ v4_pre_topc(sK3,sK2)
    | ~ r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_47,plain,
    ( v4_pre_topc(sK3,sK2) != iProver_top
    | r2_hidden(sK5,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5645,c_5500,c_47])).


%------------------------------------------------------------------------------
