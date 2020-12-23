%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT2064+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:07 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  289 (1397 expanded)
%              Number of clauses        :  206 ( 335 expanded)
%              Number of leaves         :   20 ( 392 expanded)
%              Depth                    :   21
%              Number of atoms          : 1862 (20851 expanded)
%              Number of equality atoms :  114 ( 175 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   42 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,conjecture,(
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
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_pre_topc(X0,X1))
                <=> ? [X3] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X3))
                      & r1_waybel_0(X0,X3,X1)
                      & l1_waybel_0(X3,X0)
                      & v3_yellow_6(X3,X0)
                      & v7_waybel_0(X3)
                      & v4_orders_2(X3)
                      & ~ v2_struct_0(X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <~> ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                    | ~ r1_waybel_0(X0,X3,X1)
                    | ~ l1_waybel_0(X3,X0)
                    | ~ v3_yellow_6(X3,X0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                    | ~ r1_waybel_0(X0,X3,X1)
                    | ~ l1_waybel_0(X3,X0)
                    | ~ v3_yellow_6(X3,X0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X3] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X3))
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v3_yellow_6(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                    | ~ r1_waybel_0(X0,X3,X1)
                    | ~ l1_waybel_0(X3,X0)
                    | ~ v3_yellow_6(X3,X0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X4))
                    & r1_waybel_0(X0,X4,X1)
                    & l1_waybel_0(X4,X0)
                    & v3_yellow_6(X4,X0)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X2,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK5))
        & r1_waybel_0(X0,sK5,X1)
        & l1_waybel_0(sK5,X0)
        & v3_yellow_6(sK5,X0)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                | ~ r1_waybel_0(X0,X3,X1)
                | ~ l1_waybel_0(X3,X0)
                | ~ v3_yellow_6(X3,X0)
                | ~ v7_waybel_0(X3)
                | ~ v4_orders_2(X3)
                | v2_struct_0(X3) )
            | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & ( ? [X4] :
                ( r2_hidden(X2,k10_yellow_6(X0,X4))
                & r1_waybel_0(X0,X4,X1)
                & l1_waybel_0(X4,X0)
                & v3_yellow_6(X4,X0)
                & v7_waybel_0(X4)
                & v4_orders_2(X4)
                & ~ v2_struct_0(X4) )
            | r2_hidden(X2,k2_pre_topc(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(sK4,k10_yellow_6(X0,X3))
              | ~ r1_waybel_0(X0,X3,X1)
              | ~ l1_waybel_0(X3,X0)
              | ~ v3_yellow_6(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ r2_hidden(sK4,k2_pre_topc(X0,X1)) )
        & ( ? [X4] :
              ( r2_hidden(sK4,k10_yellow_6(X0,X4))
              & r1_waybel_0(X0,X4,X1)
              & l1_waybel_0(X4,X0)
              & v3_yellow_6(X4,X0)
              & v7_waybel_0(X4)
              & v4_orders_2(X4)
              & ~ v2_struct_0(X4) )
          | r2_hidden(sK4,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                    | ~ r1_waybel_0(X0,X3,X1)
                    | ~ l1_waybel_0(X3,X0)
                    | ~ v3_yellow_6(X3,X0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & ( ? [X4] :
                    ( r2_hidden(X2,k10_yellow_6(X0,X4))
                    & r1_waybel_0(X0,X4,X1)
                    & l1_waybel_0(X4,X0)
                    & v3_yellow_6(X4,X0)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                | r2_hidden(X2,k2_pre_topc(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                  | ~ r1_waybel_0(X0,X3,sK3)
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v3_yellow_6(X3,X0)
                  | ~ v7_waybel_0(X3)
                  | ~ v4_orders_2(X3)
                  | v2_struct_0(X3) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK3)) )
            & ( ? [X4] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X4))
                  & r1_waybel_0(X0,X4,sK3)
                  & l1_waybel_0(X4,X0)
                  & v3_yellow_6(X4,X0)
                  & v7_waybel_0(X4)
                  & v4_orders_2(X4)
                  & ~ v2_struct_0(X4) )
              | r2_hidden(X2,k2_pre_topc(X0,sK3)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X3))
                      | ~ r1_waybel_0(X0,X3,X1)
                      | ~ l1_waybel_0(X3,X0)
                      | ~ v3_yellow_6(X3,X0)
                      | ~ v7_waybel_0(X3)
                      | ~ v4_orders_2(X3)
                      | v2_struct_0(X3) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & ( ? [X4] :
                      ( r2_hidden(X2,k10_yellow_6(X0,X4))
                      & r1_waybel_0(X0,X4,X1)
                      & l1_waybel_0(X4,X0)
                      & v3_yellow_6(X4,X0)
                      & v7_waybel_0(X4)
                      & v4_orders_2(X4)
                      & ~ v2_struct_0(X4) )
                  | r2_hidden(X2,k2_pre_topc(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( ~ r2_hidden(X2,k10_yellow_6(sK2,X3))
                    | ~ r1_waybel_0(sK2,X3,X1)
                    | ~ l1_waybel_0(X3,sK2)
                    | ~ v3_yellow_6(X3,sK2)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & ( ? [X4] :
                    ( r2_hidden(X2,k10_yellow_6(sK2,X4))
                    & r1_waybel_0(sK2,X4,X1)
                    & l1_waybel_0(X4,sK2)
                    & v3_yellow_6(X4,sK2)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                | r2_hidden(X2,k2_pre_topc(sK2,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK4,k10_yellow_6(sK2,X3))
          | ~ r1_waybel_0(sK2,X3,sK3)
          | ~ l1_waybel_0(X3,sK2)
          | ~ v3_yellow_6(X3,sK2)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & ( ( r2_hidden(sK4,k10_yellow_6(sK2,sK5))
        & r1_waybel_0(sK2,sK5,sK3)
        & l1_waybel_0(sK5,sK2)
        & v3_yellow_6(sK5,sK2)
        & v7_waybel_0(sK5)
        & v4_orders_2(sK5)
        & ~ v2_struct_0(sK5) )
      | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f43,f47,f46,f45,f44])).

fof(f74,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
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
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_yellow_6(X1,X0)
          <=> k10_yellow_6(X0,X1) != k1_xboole_0 )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_yellow_6(X1,X0)
              | k10_yellow_6(X0,X1) = k1_xboole_0 )
            & ( k10_yellow_6(X0,X1) != k1_xboole_0
              | ~ v3_yellow_6(X1,X0) ) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k10_yellow_6(X0,X1) = k1_xboole_0
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v3_yellow_6(X1,X0)
      | k10_yellow_6(X0,X1) = o_0_0_xboole_0
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f84,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK4,k10_yellow_6(sK2,X3))
      | ~ r1_waybel_0(sK2,X3,sK3)
      | ~ l1_waybel_0(X3,sK2)
      | ~ v3_yellow_6(X3,sK2)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,
    ( v4_orders_2(sK5)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,
    ( r1_waybel_0(sK2,sK5,sK3)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,
    ( l1_waybel_0(sK5,sK2)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,
    ( v7_waybel_0(sK5)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,
    ( ~ v2_struct_0(sK5)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,
    ( r2_hidden(sK4,k10_yellow_6(sK2,sK5))
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f67,plain,(
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

fof(f8,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK0(X0,X1,X2),X1)
        & l1_waybel_0(sK0(X0,X1,X2),X0)
        & v7_waybel_0(sK0(X0,X1,X2))
        & v4_orders_2(sK0(X0,X1,X2))
        & ~ v2_struct_0(sK0(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
                & ( ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK0(X0,X1,X2),X1)
                    & l1_waybel_0(sK0(X0,X1,X2),X0)
                    & v7_waybel_0(sK0(X0,X1,X2))
                    & v4_orders_2(sK0(X0,X1,X2))
                    & ~ v2_struct_0(sK0(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
         => ( r1_waybel_0(X0,X2,X1)
           => ! [X3] :
                ( m2_yellow_6(X3,X0,X2)
               => r1_waybel_0(X0,X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( r1_waybel_0(X0,X3,X1)
              | ~ m2_yellow_6(X3,X0,X2) )
          | ~ r1_waybel_0(X0,X2,X1)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( r1_waybel_0(X0,X3,X1)
              | ~ m2_yellow_6(X3,X0,X2) )
          | ~ r1_waybel_0(X0,X2,X1)
          | ~ l1_waybel_0(X2,X0)
          | ~ v7_waybel_0(X2)
          | ~ v4_orders_2(X2)
          | v2_struct_0(X2) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X3,X1)
      | ~ m2_yellow_6(X3,X0,X2)
      | ~ r1_waybel_0(X0,X2,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
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

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
        & m2_yellow_6(sK1(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
                & m2_yellow_6(sK1(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f39])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK1(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK0(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK0(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK0(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_6,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_434,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_2])).

cnf(c_435,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1081,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_435,c_32])).

cnf(c_1082,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1081])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1084,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(X0)
    | ~ l1_waybel_0(X1,sK2)
    | ~ m2_yellow_6(X0,sK2,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1082,c_34])).

cnf(c_1085,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | ~ v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1084])).

cnf(c_2128,plain,
    ( ~ m2_yellow_6(X0_53,sK2,X1_53)
    | ~ l1_waybel_0(X1_53,sK2)
    | ~ v2_struct_0(X0_53)
    | v2_struct_0(X1_53)
    | ~ v4_orders_2(X1_53)
    | ~ v7_waybel_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_1085])).

cnf(c_3810,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2,X0_53)
    | ~ l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X0_53)
    | ~ v2_struct_0(sK1(sK2,sK0(sK2,X0_54,sK4),sK4))
    | ~ v4_orders_2(X0_53)
    | ~ v7_waybel_0(X0_53) ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_3951,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2,sK0(sK2,X1_54,sK4))
    | ~ l1_waybel_0(sK0(sK2,X1_54,sK4),sK2)
    | ~ v2_struct_0(sK1(sK2,sK0(sK2,X0_54,sK4),sK4))
    | v2_struct_0(sK0(sK2,X1_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X1_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X1_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_3810])).

cnf(c_3953,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2,sK0(sK2,sK3,sK4))
    | ~ l1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | ~ v2_struct_0(sK1(sK2,sK0(sK2,sK3,sK4),sK4))
    | v2_struct_0(sK0(sK2,sK3,sK4))
    | ~ v4_orders_2(sK0(sK2,sK3,sK4))
    | ~ v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3951])).

cnf(c_0,plain,
    ( ~ l1_waybel_0(X0,X1)
    | v3_yellow_6(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(X1,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_22,negated_conjecture,
    ( ~ r1_waybel_0(sK2,X0,sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v3_yellow_6(X0,sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_593,plain,
    ( ~ r1_waybel_0(sK2,X0,sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_waybel_0(X0,sK2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X1)
    | ~ v7_waybel_0(X0)
    | X0 != X1
    | k10_yellow_6(X2,X1) = o_0_0_xboole_0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_594,plain,
    ( ~ r1_waybel_0(sK2,X0,sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK2,X0) = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_598,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK2)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r1_waybel_0(sK2,X0,sK3)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK2,X0) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_594,c_34,c_33,c_32])).

cnf(c_599,plain,
    ( ~ r1_waybel_0(sK2,X0,sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0)
    | k10_yellow_6(sK2,X0) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_598])).

cnf(c_2143,plain,
    ( ~ r1_waybel_0(sK2,X0_53,sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,X0_53))
    | ~ l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X0_53)
    | ~ v4_orders_2(X0_53)
    | ~ v7_waybel_0(X0_53)
    | k10_yellow_6(sK2,X0_53) = o_0_0_xboole_0 ),
    inference(subtyping,[status(esa)],[c_599])).

cnf(c_3585,plain,
    ( ~ r1_waybel_0(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4)))
    | ~ l1_waybel_0(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2)
    | v2_struct_0(sK1(sK2,sK0(sK2,X0_54,sK4),sK4))
    | ~ v4_orders_2(sK1(sK2,sK0(sK2,X0_54,sK4),sK4))
    | ~ v7_waybel_0(sK1(sK2,sK0(sK2,X0_54,sK4),sK4))
    | k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_3587,plain,
    ( ~ r1_waybel_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4)))
    | ~ l1_waybel_0(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2)
    | v2_struct_0(sK1(sK2,sK0(sK2,sK3,sK4),sK4))
    | ~ v4_orders_2(sK1(sK2,sK0(sK2,sK3,sK4),sK4))
    | ~ v7_waybel_0(sK1(sK2,sK0(sK2,sK3,sK4),sK4))
    | k10_yellow_6(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4)) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3585])).

cnf(c_2160,plain,
    ( ~ v1_xboole_0(X0_55)
    | v1_xboole_0(X1_55)
    | X1_55 != X0_55 ),
    theory(equality)).

cnf(c_3554,plain,
    ( ~ v1_xboole_0(X0_55)
    | v1_xboole_0(k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4)))
    | k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4)) != X0_55 ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_3556,plain,
    ( v1_xboole_0(k10_yellow_6(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4)))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k10_yellow_6(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4)) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3554])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2148,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | v4_orders_2(sK5) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2681,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v4_orders_2(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2148])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2155,plain,
    ( ~ r2_hidden(X0_54,X0_55)
    | m1_subset_1(X0_54,X0_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2674,plain,
    ( r2_hidden(X0_54,X0_55) != iProver_top
    | m1_subset_1(X0_54,X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2155])).

cnf(c_3157,plain,
    ( m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v4_orders_2(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_2674])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3044,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2155])).

cnf(c_3045,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3044])).

cnf(c_24,negated_conjecture,
    ( r1_waybel_0(sK2,sK5,sK3)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2151,negated_conjecture,
    ( r1_waybel_0(sK2,sK5,sK3)
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2678,plain,
    ( r1_waybel_0(sK2,sK5,sK3) = iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2151])).

cnf(c_3155,plain,
    ( r1_waybel_0(sK2,sK5,sK3) = iProver_top
    | m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2678,c_2674])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | l1_waybel_0(sK5,sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2150,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | l1_waybel_0(sK5,sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2679,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | l1_waybel_0(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2150])).

cnf(c_3156,plain,
    ( m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | l1_waybel_0(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2679,c_2674])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | v7_waybel_0(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2149,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | v7_waybel_0(sK5) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2680,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v7_waybel_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2149])).

cnf(c_3158,plain,
    ( m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v7_waybel_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2680,c_2674])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2147,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v2_struct_0(sK5) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2682,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2147])).

cnf(c_3159,plain,
    ( m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | v2_struct_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_2674])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | r2_hidden(sK4,k10_yellow_6(sK2,sK5)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2152,negated_conjecture,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | r2_hidden(sK4,k10_yellow_6(sK2,sK5)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2677,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2152])).

cnf(c_3239,plain,
    ( r2_hidden(sK4,k10_yellow_6(sK2,sK5)) = iProver_top
    | m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2674])).

cnf(c_17,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_819,plain,
    ( r3_waybel_9(X0,X1,X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_820,plain,
    ( r3_waybel_9(sK2,X0,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_819])).

cnf(c_824,plain,
    ( v2_struct_0(X0)
    | r3_waybel_9(sK2,X0,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_820,c_34,c_32])).

cnf(c_825,plain,
    ( r3_waybel_9(sK2,X0,X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK2,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_824])).

cnf(c_2135,plain,
    ( r3_waybel_9(sK2,X0_53,X0_54)
    | ~ r2_hidden(X0_54,k10_yellow_6(sK2,X0_53))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X0_53)
    | ~ v4_orders_2(X0_53)
    | ~ v7_waybel_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_825])).

cnf(c_3088,plain,
    ( r3_waybel_9(sK2,sK5,X0_54)
    | ~ r2_hidden(X0_54,k10_yellow_6(sK2,sK5))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2135])).

cnf(c_3338,plain,
    ( r3_waybel_9(sK2,sK5,sK4)
    | ~ r2_hidden(sK4,k10_yellow_6(sK2,sK5))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3088])).

cnf(c_3339,plain,
    ( r3_waybel_9(sK2,sK5,sK4) = iProver_top
    | r2_hidden(sK4,k10_yellow_6(sK2,sK5)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | l1_waybel_0(sK5,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3338])).

cnf(c_10,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_900,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | ~ r1_waybel_0(X0,X1,X3)
    | r2_hidden(X2,k2_pre_topc(X0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_33])).

cnf(c_901,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | ~ r1_waybel_0(sK2,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_900])).

cnf(c_905,plain,
    ( v2_struct_0(X0)
    | ~ r3_waybel_9(sK2,X0,X1)
    | ~ r1_waybel_0(sK2,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_901,c_34,c_32])).

cnf(c_906,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | ~ r1_waybel_0(sK2,X0,X2)
    | r2_hidden(X1,k2_pre_topc(sK2,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_905])).

cnf(c_2132,plain,
    ( ~ r3_waybel_9(sK2,X0_53,X0_54)
    | ~ r1_waybel_0(sK2,X0_53,X1_54)
    | r2_hidden(X0_54,k2_pre_topc(sK2,X1_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X0_53)
    | ~ v4_orders_2(X0_53)
    | ~ v7_waybel_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_906])).

cnf(c_3084,plain,
    ( ~ r3_waybel_9(sK2,sK5,X0_54)
    | ~ r1_waybel_0(sK2,sK5,X1_54)
    | r2_hidden(X0_54,k2_pre_topc(sK2,X1_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_3408,plain,
    ( ~ r3_waybel_9(sK2,sK5,sK4)
    | ~ r1_waybel_0(sK2,sK5,X0_54)
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v7_waybel_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3084])).

cnf(c_3415,plain,
    ( r3_waybel_9(sK2,sK5,sK4) != iProver_top
    | r1_waybel_0(sK2,sK5,X0_54) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,X0_54)) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | l1_waybel_0(sK5,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3408])).

cnf(c_3417,plain,
    ( r3_waybel_9(sK2,sK5,sK4) != iProver_top
    | r1_waybel_0(sK2,sK5,sK3) != iProver_top
    | r2_hidden(sK4,k2_pre_topc(sK2,sK3)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | l1_waybel_0(sK5,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v4_orders_2(sK5) != iProver_top
    | v7_waybel_0(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3415])).

cnf(c_3533,plain,
    ( m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3157,c_38,c_39,c_3045,c_3155,c_3156,c_3158,c_3159,c_3239,c_3339,c_3417])).

cnf(c_3535,plain,
    ( m1_subset_1(sK4,k2_pre_topc(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3533])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2153,plain,
    ( ~ r2_hidden(X0_54,X0_55)
    | ~ v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2676,plain,
    ( r2_hidden(X0_54,X0_55) != iProver_top
    | v1_xboole_0(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2153])).

cnf(c_3238,plain,
    ( r2_hidden(sK4,k10_yellow_6(sK2,sK5)) = iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2677,c_2676])).

cnf(c_3041,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ v1_xboole_0(k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2153])).

cnf(c_3042,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3)) != iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3041])).

cnf(c_3205,plain,
    ( r1_waybel_0(sK2,sK5,sK3) = iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2678,c_2676])).

cnf(c_3206,plain,
    ( l1_waybel_0(sK5,sK2) = iProver_top
    | v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2679,c_2676])).

cnf(c_3207,plain,
    ( v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top
    | v4_orders_2(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2681,c_2676])).

cnf(c_3208,plain,
    ( v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top
    | v7_waybel_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2680,c_2676])).

cnf(c_3209,plain,
    ( v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top
    | v2_struct_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_2676])).

cnf(c_3474,plain,
    ( v1_xboole_0(k2_pre_topc(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3238,c_38,c_39,c_3042,c_3205,c_3206,c_3207,c_3208,c_3209,c_3339,c_3417])).

cnf(c_3476,plain,
    ( ~ v1_xboole_0(k2_pre_topc(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3474])).

cnf(c_9,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X3,X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_404,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X3,X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_1107,plain,
    ( ~ r1_waybel_0(X0,X1,X2)
    | r1_waybel_0(X0,X3,X2)
    | ~ m2_yellow_6(X3,X0,X1)
    | ~ l1_waybel_0(X1,X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_404,c_32])).

cnf(c_1108,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | r1_waybel_0(sK2,X2,X1)
    | ~ m2_yellow_6(X2,sK2,X0)
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1107])).

cnf(c_1110,plain,
    ( v2_struct_0(X0)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m2_yellow_6(X2,sK2,X0)
    | r1_waybel_0(sK2,X2,X1)
    | ~ r1_waybel_0(sK2,X0,X1)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1108,c_34])).

cnf(c_1111,plain,
    ( ~ r1_waybel_0(sK2,X0,X1)
    | r1_waybel_0(sK2,X2,X1)
    | ~ m2_yellow_6(X2,sK2,X0)
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1110])).

cnf(c_2127,plain,
    ( ~ r1_waybel_0(sK2,X0_53,X0_54)
    | r1_waybel_0(sK2,X1_53,X0_54)
    | ~ m2_yellow_6(X1_53,sK2,X0_53)
    | ~ l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X0_53)
    | ~ v4_orders_2(X0_53)
    | ~ v7_waybel_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_1111])).

cnf(c_3264,plain,
    ( r1_waybel_0(sK2,X0_53,X0_54)
    | ~ r1_waybel_0(sK2,sK0(sK2,X1_54,sK4),X0_54)
    | ~ m2_yellow_6(X0_53,sK2,sK0(sK2,X1_54,sK4))
    | ~ l1_waybel_0(sK0(sK2,X1_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X1_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X1_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X1_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_3449,plain,
    ( r1_waybel_0(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4),X1_54)
    | ~ r1_waybel_0(sK2,sK0(sK2,X0_54,sK4),X1_54)
    | ~ m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2,sK0(sK2,X0_54,sK4))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_3451,plain,
    ( r1_waybel_0(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK3)
    | ~ r1_waybel_0(sK2,sK0(sK2,sK3,sK4),sK3)
    | ~ m2_yellow_6(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2,sK0(sK2,sK3,sK4))
    | ~ l1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | v2_struct_0(sK0(sK2,sK3,sK4))
    | ~ v4_orders_2(sK0(sK2,sK3,sK4))
    | ~ v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3449])).

cnf(c_5,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_462,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_2])).

cnf(c_463,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_1055,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_463,c_32])).

cnf(c_1056,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1055])).

cnf(c_1058,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK2)
    | ~ m2_yellow_6(X0,sK2,X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1056,c_34])).

cnf(c_1059,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | v4_orders_2(X0)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1058])).

cnf(c_2129,plain,
    ( ~ m2_yellow_6(X0_53,sK2,X1_53)
    | ~ l1_waybel_0(X1_53,sK2)
    | v2_struct_0(X1_53)
    | ~ v4_orders_2(X1_53)
    | v4_orders_2(X0_53)
    | ~ v7_waybel_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_1059])).

cnf(c_3293,plain,
    ( ~ m2_yellow_6(X0_53,sK2,sK0(sK2,X0_54,sK4))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | v4_orders_2(X0_53)
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_3434,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2,sK0(sK2,X0_54,sK4))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | v4_orders_2(sK1(sK2,sK0(sK2,X0_54,sK4),sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_3293])).

cnf(c_3446,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2,sK0(sK2,sK3,sK4))
    | ~ l1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | v2_struct_0(sK0(sK2,sK3,sK4))
    | v4_orders_2(sK1(sK2,sK0(sK2,sK3,sK4),sK4))
    | ~ v4_orders_2(sK0(sK2,sK3,sK4))
    | ~ v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3434])).

cnf(c_4,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_490,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2])).

cnf(c_491,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_1029,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | v7_waybel_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_491,c_32])).

cnf(c_1030,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_1029])).

cnf(c_1032,plain,
    ( v2_struct_0(X1)
    | ~ l1_waybel_0(X1,sK2)
    | ~ m2_yellow_6(X0,sK2,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1030,c_34])).

cnf(c_1033,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_1032])).

cnf(c_2130,plain,
    ( ~ m2_yellow_6(X0_53,sK2,X1_53)
    | ~ l1_waybel_0(X1_53,sK2)
    | v2_struct_0(X1_53)
    | ~ v4_orders_2(X1_53)
    | ~ v7_waybel_0(X1_53)
    | v7_waybel_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_1033])).

cnf(c_3292,plain,
    ( ~ m2_yellow_6(X0_53,sK2,sK0(sK2,X0_54,sK4))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | v7_waybel_0(X0_53)
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2130])).

cnf(c_3435,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2,sK0(sK2,X0_54,sK4))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | v7_waybel_0(sK1(sK2,sK0(sK2,X0_54,sK4),sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_3292])).

cnf(c_3442,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2,sK0(sK2,sK3,sK4))
    | ~ l1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | v2_struct_0(sK0(sK2,sK3,sK4))
    | ~ v4_orders_2(sK0(sK2,sK3,sK4))
    | v7_waybel_0(sK1(sK2,sK0(sK2,sK3,sK4),sK4))
    | ~ v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3435])).

cnf(c_3,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_518,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | X3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_2])).

cnf(c_519,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_1003,plain,
    ( ~ m2_yellow_6(X0,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | l1_waybel_0(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_519,c_32])).

cnf(c_1004,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | l1_waybel_0(X0,sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(unflattening,[status(thm)],[c_1003])).

cnf(c_1006,plain,
    ( v2_struct_0(X1)
    | l1_waybel_0(X0,sK2)
    | ~ l1_waybel_0(X1,sK2)
    | ~ m2_yellow_6(X0,sK2,X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1004,c_34])).

cnf(c_1007,plain,
    ( ~ m2_yellow_6(X0,sK2,X1)
    | ~ l1_waybel_0(X1,sK2)
    | l1_waybel_0(X0,sK2)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(renaming,[status(thm)],[c_1006])).

cnf(c_2131,plain,
    ( ~ m2_yellow_6(X0_53,sK2,X1_53)
    | ~ l1_waybel_0(X1_53,sK2)
    | l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X1_53)
    | ~ v4_orders_2(X1_53)
    | ~ v7_waybel_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_1007])).

cnf(c_3291,plain,
    ( ~ m2_yellow_6(X0_53,sK2,sK0(sK2,X0_54,sK4))
    | l1_waybel_0(X0_53,sK2)
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_3436,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2,sK0(sK2,X0_54,sK4))
    | l1_waybel_0(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2)
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_3291])).

cnf(c_3438,plain,
    ( ~ m2_yellow_6(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2,sK0(sK2,sK3,sK4))
    | l1_waybel_0(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2)
    | ~ l1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | v2_struct_0(sK0(sK2,sK3,sK4))
    | ~ v4_orders_2(sK0(sK2,sK3,sK4))
    | ~ v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3436])).

cnf(c_3421,plain,
    ( ~ r2_hidden(sK4,k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4)))
    | ~ v1_xboole_0(k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4))) ),
    inference(instantiation,[status(thm)],[c_2153])).

cnf(c_3423,plain,
    ( ~ r2_hidden(sK4,k10_yellow_6(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4)))
    | ~ v1_xboole_0(k10_yellow_6(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4))) ),
    inference(instantiation,[status(thm)],[c_3421])).

cnf(c_19,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_786,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | r2_hidden(X2,k10_yellow_6(X0,sK1(X0,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_33])).

cnf(c_787,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_791,plain,
    ( v2_struct_0(X0)
    | ~ r3_waybel_9(sK2,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_34,c_32])).

cnf(c_792,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | r2_hidden(X1,k10_yellow_6(sK2,sK1(sK2,X0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_791])).

cnf(c_2136,plain,
    ( ~ r3_waybel_9(sK2,X0_53,X0_54)
    | r2_hidden(X0_54,k10_yellow_6(sK2,sK1(sK2,X0_53,X0_54)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X0_53)
    | ~ v4_orders_2(X0_53)
    | ~ v7_waybel_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_792])).

cnf(c_3263,plain,
    ( ~ r3_waybel_9(sK2,sK0(sK2,X0_54,sK4),X1_54)
    | r2_hidden(X1_54,k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),X1_54)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_3392,plain,
    ( ~ r3_waybel_9(sK2,sK0(sK2,X0_54,sK4),sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,sK1(sK2,sK0(sK2,X0_54,sK4),sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_3394,plain,
    ( ~ r3_waybel_9(sK2,sK0(sK2,sK3,sK4),sK4)
    | r2_hidden(sK4,k10_yellow_6(sK2,sK1(sK2,sK0(sK2,sK3,sK4),sK4)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | v2_struct_0(sK0(sK2,sK3,sK4))
    | ~ v4_orders_2(sK0(sK2,sK3,sK4))
    | ~ v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3392])).

cnf(c_20,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_753,plain,
    ( ~ r3_waybel_9(X0,X1,X2)
    | m2_yellow_6(sK1(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_waybel_0(X1,X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X1)
    | ~ v7_waybel_0(X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_754,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | m2_yellow_6(sK1(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(unflattening,[status(thm)],[c_753])).

cnf(c_758,plain,
    ( v2_struct_0(X0)
    | ~ r3_waybel_9(sK2,X0,X1)
    | m2_yellow_6(sK1(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_754,c_34,c_32])).

cnf(c_759,plain,
    ( ~ r3_waybel_9(sK2,X0,X1)
    | m2_yellow_6(sK1(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0,sK2)
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v7_waybel_0(X0) ),
    inference(renaming,[status(thm)],[c_758])).

cnf(c_2137,plain,
    ( ~ r3_waybel_9(sK2,X0_53,X0_54)
    | m2_yellow_6(sK1(sK2,X0_53,X0_54),sK2,X0_53)
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(X0_53,sK2)
    | v2_struct_0(X0_53)
    | ~ v4_orders_2(X0_53)
    | ~ v7_waybel_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_759])).

cnf(c_3262,plain,
    ( ~ r3_waybel_9(sK2,sK0(sK2,X0_54,sK4),X1_54)
    | m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),X1_54),sK2,sK0(sK2,X0_54,sK4))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2137])).

cnf(c_3387,plain,
    ( ~ r3_waybel_9(sK2,sK0(sK2,X0_54,sK4),sK4)
    | m2_yellow_6(sK1(sK2,sK0(sK2,X0_54,sK4),sK4),sK2,sK0(sK2,X0_54,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK0(sK2,X0_54,sK4),sK2)
    | v2_struct_0(sK0(sK2,X0_54,sK4))
    | ~ v4_orders_2(sK0(sK2,X0_54,sK4))
    | ~ v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_3262])).

cnf(c_3389,plain,
    ( ~ r3_waybel_9(sK2,sK0(sK2,sK3,sK4),sK4)
    | m2_yellow_6(sK1(sK2,sK0(sK2,sK3,sK4),sK4),sK2,sK0(sK2,sK3,sK4))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_waybel_0(sK0(sK2,sK3,sK4),sK2)
    | v2_struct_0(sK0(sK2,sK3,sK4))
    | ~ v4_orders_2(sK0(sK2,sK3,sK4))
    | ~ v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3387])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2154,plain,
    ( r2_hidden(X0_54,X0_55)
    | ~ m1_subset_1(X0_54,X0_55)
    | v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3073,plain,
    ( r2_hidden(X0_54,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(X0_54,k2_pre_topc(sK2,sK3))
    | v1_xboole_0(k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_3343,plain,
    ( r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK4,k2_pre_topc(sK2,sK3))
    | v1_xboole_0(k2_pre_topc(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3073])).

cnf(c_12,plain,
    ( r1_waybel_0(X0,sK0(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_852,plain,
    ( r1_waybel_0(X0,sK0(X0,X1,X2),X1)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_853,plain,
    ( r1_waybel_0(sK2,sK0(sK2,X0,X1),X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_852])).

cnf(c_857,plain,
    ( r1_waybel_0(sK2,sK0(sK2,X0,X1),X0)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_853,c_34,c_32])).

cnf(c_2134,plain,
    ( r1_waybel_0(sK2,sK0(sK2,X0_54,X1_54),X0_54)
    | ~ r2_hidden(X1_54,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_857])).

cnf(c_3031,plain,
    ( r1_waybel_0(sK2,sK0(sK2,X0_54,sK4),X0_54)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2134])).

cnf(c_3033,plain,
    ( r1_waybel_0(sK2,sK0(sK2,sK3,sK4),sK3)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3031])).

cnf(c_11,plain,
    ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_876,plain,
    ( r3_waybel_9(X0,sK0(X0,X1,X2),X2)
    | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_877,plain,
    ( r3_waybel_9(sK2,sK0(sK2,X0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_876])).

cnf(c_881,plain,
    ( r3_waybel_9(sK2,sK0(sK2,X0,X1),X1)
    | ~ r2_hidden(X1,k2_pre_topc(sK2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_877,c_34,c_32])).

cnf(c_2133,plain,
    ( r3_waybel_9(sK2,sK0(sK2,X0_54,X1_54),X1_54)
    | ~ r2_hidden(X1_54,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_54,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_881])).

cnf(c_3026,plain,
    ( r3_waybel_9(sK2,sK0(sK2,X0_54,sK4),sK4)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_3028,plain,
    ( r3_waybel_9(sK2,sK0(sK2,sK3,sK4),sK4)
    | ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_657,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(sK0(X1,X2,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_658,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_struct_0(sK0(sK2,X1,X0))
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_657])).

cnf(c_662,plain,
    ( ~ v2_struct_0(sK0(sK2,X1,X0))
    | ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_658,c_34,c_32])).

cnf(c_663,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ v2_struct_0(sK0(sK2,X1,X0)) ),
    inference(renaming,[status(thm)],[c_662])).

cnf(c_2141,plain,
    ( ~ r2_hidden(X0_54,k2_pre_topc(sK2,X1_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | ~ v2_struct_0(sK0(sK2,X1_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_663])).

cnf(c_3021,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v2_struct_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_3023,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v2_struct_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3021])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v4_orders_2(sK0(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_681,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v4_orders_2(sK0(X1,X2,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_682,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v4_orders_2(sK0(sK2,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_686,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v4_orders_2(sK0(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_34,c_32])).

cnf(c_2140,plain,
    ( ~ r2_hidden(X0_54,k2_pre_topc(sK2,X1_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | v4_orders_2(sK0(sK2,X1_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_686])).

cnf(c_3016,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v4_orders_2(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_3018,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v4_orders_2(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3016])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(sK0(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_705,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(sK0(X1,X2,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_706,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v7_waybel_0(sK0(sK2,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_710,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v7_waybel_0(sK0(sK2,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_706,c_34,c_32])).

cnf(c_2139,plain,
    ( ~ r2_hidden(X0_54,k2_pre_topc(sK2,X1_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | v7_waybel_0(sK0(sK2,X1_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_710])).

cnf(c_3011,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v7_waybel_0(sK0(sK2,X0_54,sK4)) ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3013,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v7_waybel_0(sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3011])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | l1_waybel_0(sK0(X1,X2,X0),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_729,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | l1_waybel_0(sK0(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_730,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | l1_waybel_0(sK0(sK2,X1,X0),sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_734,plain,
    ( ~ r2_hidden(X0,k2_pre_topc(sK2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | l1_waybel_0(sK0(sK2,X1,X0),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_34,c_32])).

cnf(c_2138,plain,
    ( ~ r2_hidden(X0_54,k2_pre_topc(sK2,X1_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0_54,u1_struct_0(sK2))
    | l1_waybel_0(sK0(sK2,X1_54,X0_54),sK2) ),
    inference(subtyping,[status(esa)],[c_734])).

cnf(c_3006,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,X0_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | l1_waybel_0(sK0(sK2,X0_54,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_3008,plain,
    ( ~ r2_hidden(sK4,k2_pre_topc(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | l1_waybel_0(sK0(sK2,sK3,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_3006])).

cnf(c_7,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3953,c_3587,c_3556,c_3535,c_3476,c_3451,c_3446,c_3442,c_3438,c_3423,c_3394,c_3389,c_3343,c_3033,c_3028,c_3023,c_3018,c_3013,c_3008,c_7,c_30,c_31])).


%------------------------------------------------------------------------------
