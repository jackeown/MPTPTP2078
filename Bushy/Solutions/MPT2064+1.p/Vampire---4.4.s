%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t24_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 36.56s
% Output     : Refutation 36.56s
% Verified   : 
% Statistics : Number of formulae       :  291 (11305 expanded)
%              Number of leaves         :   19 (3730 expanded)
%              Depth                    :   93
%              Number of atoms          : 2362 (193323 expanded)
%              Number of equality atoms :    8 (  56 expanded)
%              Maximal formula depth    :   23 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1558,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1557,f1478])).

fof(f1478,plain,(
    l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f1464,f253])).

fof(f253,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f252,f100])).

fof(f100,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
          | ~ r1_waybel_0(sK0,X3,sK1)
          | ~ l1_waybel_0(X3,sK0)
          | ~ v3_yellow_6(X3,sK0)
          | ~ v7_waybel_0(X3)
          | ~ v4_orders_2(X3)
          | v2_struct_0(X3) )
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & ( ( r2_hidden(sK2,k10_yellow_6(sK0,sK3))
        & r1_waybel_0(sK0,sK3,sK1)
        & l1_waybel_0(sK3,sK0)
        & v3_yellow_6(sK3,sK0)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) )
      | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f75,f79,f78,f77,f76])).

fof(f76,plain,
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
                    ( ~ r2_hidden(X2,k10_yellow_6(sK0,X3))
                    | ~ r1_waybel_0(sK0,X3,X1)
                    | ~ l1_waybel_0(X3,sK0)
                    | ~ v3_yellow_6(X3,sK0)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                | ~ r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & ( ? [X4] :
                    ( r2_hidden(X2,k10_yellow_6(sK0,X4))
                    & r1_waybel_0(sK0,X4,X1)
                    & l1_waybel_0(X4,sK0)
                    & v3_yellow_6(X4,sK0)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                | r2_hidden(X2,k2_pre_topc(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
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
                  | ~ r1_waybel_0(X0,X3,sK1)
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v3_yellow_6(X3,X0)
                  | ~ v7_waybel_0(X3)
                  | ~ v4_orders_2(X3)
                  | v2_struct_0(X3) )
              | ~ r2_hidden(X2,k2_pre_topc(X0,sK1)) )
            & ( ? [X4] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X4))
                  & r1_waybel_0(X0,X4,sK1)
                  & l1_waybel_0(X4,X0)
                  & v3_yellow_6(X4,X0)
                  & v7_waybel_0(X4)
                  & v4_orders_2(X4)
                  & ~ v2_struct_0(X4) )
              | r2_hidden(X2,k2_pre_topc(X0,sK1)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
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
              ( ~ r2_hidden(sK2,k10_yellow_6(X0,X3))
              | ~ r1_waybel_0(X0,X3,X1)
              | ~ l1_waybel_0(X3,X0)
              | ~ v3_yellow_6(X3,X0)
              | ~ v7_waybel_0(X3)
              | ~ v4_orders_2(X3)
              | v2_struct_0(X3) )
          | ~ r2_hidden(sK2,k2_pre_topc(X0,X1)) )
        & ( ? [X4] :
              ( r2_hidden(sK2,k10_yellow_6(X0,X4))
              & r1_waybel_0(X0,X4,X1)
              & l1_waybel_0(X4,X0)
              & v3_yellow_6(X4,X0)
              & v7_waybel_0(X4)
              & v4_orders_2(X4)
              & ~ v2_struct_0(X4) )
          | r2_hidden(sK2,k2_pre_topc(X0,X1)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ? [X4] :
          ( r2_hidden(X2,k10_yellow_6(X0,X4))
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v3_yellow_6(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK3))
        & r1_waybel_0(X0,sK3,X1)
        & l1_waybel_0(sK3,X0)
        & v3_yellow_6(sK3,X0)
        & v7_waybel_0(sK3)
        & v4_orders_2(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
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
    inference(rectify,[],[f74])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f73,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t24_yellow19)).

fof(f252,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f251,f101])).

fof(f101,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f251,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f250,f102])).

fof(f102,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f250,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f249,f103])).

fof(f103,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f80])).

fof(f249,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f223,f104])).

fof(f104,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f80])).

fof(f223,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_waybel_0(sK3,sK0) ),
    inference(resolution,[],[f120,f109])).

fof(f109,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | l1_waybel_0(sK3,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
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
                & ( ( r3_waybel_9(X0,sK5(X0,X1,X2),X2)
                    & r1_waybel_0(X0,sK5(X0,X1,X2),X1)
                    & l1_waybel_0(sK5(X0,X1,X2),X0)
                    & v7_waybel_0(sK5(X0,X1,X2))
                    & v4_orders_2(sK5(X0,X1,X2))
                    & ~ v2_struct_0(sK5(X0,X1,X2)) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f84,f85])).

fof(f85,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_waybel_9(X0,X4,X2)
          & r1_waybel_0(X0,X4,X1)
          & l1_waybel_0(X4,X0)
          & v7_waybel_0(X4)
          & v4_orders_2(X4)
          & ~ v2_struct_0(X4) )
     => ( r3_waybel_9(X0,sK5(X0,X1,X2),X2)
        & r1_waybel_0(X0,sK5(X0,X1,X2),X1)
        & l1_waybel_0(sK5(X0,X1,X2),X0)
        & v7_waybel_0(sK5(X0,X1,X2))
        & v4_orders_2(sK5(X0,X1,X2))
        & ~ v2_struct_0(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
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
    inference(rectify,[],[f83])).

fof(f83,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t23_yellow19)).

fof(f1464,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | l1_waybel_0(sK3,sK0) ),
    inference(resolution,[],[f1454,f109])).

fof(f1454,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK5(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1453,f100])).

fof(f1453,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1452,f101])).

fof(f1452,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1451,f102])).

fof(f1451,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1450,f103])).

fof(f1450,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1449,f104])).

fof(f1449,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1448])).

fof(f1448,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1443,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f1443,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1442,f100])).

fof(f1442,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1441,f101])).

fof(f1441,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1440,f102])).

fof(f1440,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1439,f103])).

fof(f1439,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1438,f104])).

fof(f1438,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1437])).

fof(f1437,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1432,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(sK5(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f1432,plain,
    ( ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1431,f100])).

fof(f1431,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1430,f101])).

fof(f1430,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1429,f102])).

fof(f1429,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1428,f103])).

fof(f1428,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1427,f104])).

fof(f1427,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1426])).

fof(f1426,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1421,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f1421,plain,
    ( ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1420,f100])).

fof(f1420,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1419,f101])).

fof(f1419,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1418,f102])).

fof(f1418,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1417,f104])).

fof(f1417,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1416,f103])).

fof(f1416,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1415])).

fof(f1415,plain,
    ( ~ v4_orders_2(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK5(sK0,sK1,sK2),sK0)
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1231,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f1231,plain,(
    ! [X0] :
      ( ~ r1_waybel_0(sK0,sK5(sK0,X0,sK2),sK1)
      | ~ v4_orders_2(sK5(sK0,X0,sK2))
      | v2_struct_0(sK5(sK0,X0,sK2))
      | ~ v7_waybel_0(sK5(sK0,X0,sK2))
      | ~ l1_waybel_0(sK5(sK0,X0,sK2),sK0)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1230,f100])).

fof(f1230,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK5(sK0,X0,sK2))
      | ~ v4_orders_2(sK5(sK0,X0,sK2))
      | v2_struct_0(sK5(sK0,X0,sK2))
      | ~ r1_waybel_0(sK0,sK5(sK0,X0,sK2),sK1)
      | ~ l1_waybel_0(sK5(sK0,X0,sK2),sK0)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1229,f101])).

fof(f1229,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK5(sK0,X0,sK2))
      | ~ v4_orders_2(sK5(sK0,X0,sK2))
      | v2_struct_0(sK5(sK0,X0,sK2))
      | ~ r1_waybel_0(sK0,sK5(sK0,X0,sK2),sK1)
      | ~ l1_waybel_0(sK5(sK0,X0,sK2),sK0)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1228,f102])).

fof(f1228,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK5(sK0,X0,sK2))
      | ~ v4_orders_2(sK5(sK0,X0,sK2))
      | v2_struct_0(sK5(sK0,X0,sK2))
      | ~ r1_waybel_0(sK0,sK5(sK0,X0,sK2),sK1)
      | ~ l1_waybel_0(sK5(sK0,X0,sK2),sK0)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1222,f104])).

fof(f1222,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK5(sK0,X0,sK2))
      | ~ v4_orders_2(sK5(sK0,X0,sK2))
      | v2_struct_0(sK5(sK0,X0,sK2))
      | ~ r1_waybel_0(sK0,sK5(sK0,X0,sK2),sK1)
      | ~ l1_waybel_0(sK5(sK0,X0,sK2),sK0)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,X0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f1218,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,sK5(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f1218,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,X0,sK2)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f1217,f100])).

fof(f1217,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1216,f101])).

fof(f1216,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1215,f102])).

fof(f1215,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1214,f104])).

fof(f1214,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1213])).

fof(f1213,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2) ) ),
    inference(resolution,[],[f1210,f298])).

fof(f298,plain,(
    ! [X14,X15,X13] :
      ( ~ v2_struct_0(sK6(X13,X14,X15))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | ~ l1_waybel_0(X14,X13)
      | ~ v7_waybel_0(X14)
      | ~ v4_orders_2(X14)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | ~ r3_waybel_9(X13,X14,X15) ) ),
    inference(subsumption_resolution,[],[f289,f117])).

fof(f117,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',dt_l1_pre_topc)).

fof(f289,plain,(
    ! [X14,X15,X13] :
      ( ~ r3_waybel_9(X13,X14,X15)
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | ~ l1_waybel_0(X14,X13)
      | ~ v7_waybel_0(X14)
      | ~ v4_orders_2(X14)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | ~ v2_struct_0(sK6(X13,X14,X15))
      | ~ l1_struct_0(X13) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X14,X15,X13] :
      ( ~ r3_waybel_9(X13,X14,X15)
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | ~ l1_waybel_0(X14,X13)
      | ~ v7_waybel_0(X14)
      | ~ v4_orders_2(X14)
      | v2_struct_0(X14)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | ~ v2_struct_0(sK6(X13,X14,X15))
      | ~ l1_waybel_0(X14,X13)
      | ~ v7_waybel_0(X14)
      | ~ v4_orders_2(X14)
      | v2_struct_0(X14)
      | ~ l1_struct_0(X13)
      | v2_struct_0(X13) ) ),
    inference(resolution,[],[f130,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',dt_m2_yellow_6)).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK6(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
                & m2_yellow_6(sK6(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f51,f88])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
        & m2_yellow_6(sK6(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t32_waybel_9)).

fof(f1210,plain,(
    ! [X14] :
      ( v2_struct_0(sK6(sK0,X14,sK2))
      | ~ l1_waybel_0(X14,sK0)
      | ~ v7_waybel_0(X14)
      | ~ v4_orders_2(X14)
      | v2_struct_0(X14)
      | ~ r1_waybel_0(sK0,X14,sK1)
      | ~ r3_waybel_9(sK0,X14,sK2) ) ),
    inference(subsumption_resolution,[],[f1209,f848])).

fof(f848,plain,(
    ! [X4] :
      ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | ~ r3_waybel_9(sK0,X4,sK2) ) ),
    inference(subsumption_resolution,[],[f847,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(resolution,[],[f135,f110])).

fof(f110,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f80])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t1_subset)).

fof(f847,plain,(
    ! [X4] :
      ( ~ r1_waybel_0(sK0,sK3,sK1)
      | ~ r3_waybel_9(sK0,X4,sK2)
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f846,f170])).

fof(f170,plain,
    ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
    | l1_waybel_0(sK3,sK0) ),
    inference(resolution,[],[f135,f109])).

fof(f846,plain,(
    ! [X4] :
      ( ~ r1_waybel_0(sK0,sK3,sK1)
      | ~ l1_waybel_0(sK3,sK0)
      | ~ r3_waybel_9(sK0,X4,sK2)
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f845,f171])).

fof(f171,plain,
    ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
    | v3_yellow_6(sK3,sK0) ),
    inference(resolution,[],[f135,f108])).

fof(f108,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v3_yellow_6(sK3,sK0) ),
    inference(cnf_transformation,[],[f80])).

fof(f845,plain,(
    ! [X4] :
      ( ~ r1_waybel_0(sK0,sK3,sK1)
      | ~ l1_waybel_0(sK3,sK0)
      | ~ v3_yellow_6(sK3,sK0)
      | ~ r3_waybel_9(sK0,X4,sK2)
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f844,f172])).

fof(f172,plain,
    ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
    | v7_waybel_0(sK3) ),
    inference(resolution,[],[f135,f107])).

fof(f107,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v7_waybel_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

fof(f844,plain,(
    ! [X4] :
      ( ~ r1_waybel_0(sK0,sK3,sK1)
      | ~ l1_waybel_0(sK3,sK0)
      | ~ v3_yellow_6(sK3,sK0)
      | ~ v7_waybel_0(sK3)
      | ~ r3_waybel_9(sK0,X4,sK2)
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f843,f173])).

fof(f173,plain,
    ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
    | v4_orders_2(sK3) ),
    inference(resolution,[],[f135,f106])).

fof(f106,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f80])).

fof(f843,plain,(
    ! [X4] :
      ( ~ r1_waybel_0(sK0,sK3,sK1)
      | ~ l1_waybel_0(sK3,sK0)
      | ~ v3_yellow_6(sK3,sK0)
      | ~ v7_waybel_0(sK3)
      | ~ v4_orders_2(sK3)
      | ~ r3_waybel_9(sK0,X4,sK2)
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f842,f174])).

fof(f174,plain,
    ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
    | ~ v2_struct_0(sK3) ),
    inference(resolution,[],[f135,f105])).

fof(f105,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

fof(f842,plain,(
    ! [X4] :
      ( ~ r1_waybel_0(sK0,sK3,sK1)
      | ~ l1_waybel_0(sK3,sK0)
      | ~ v3_yellow_6(sK3,sK0)
      | ~ v7_waybel_0(sK3)
      | ~ v4_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ r3_waybel_9(sK0,X4,sK2)
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f822,f208])).

fof(f208,plain,
    ( m1_subset_1(sK2,k2_pre_topc(sK0,sK1))
    | ~ v1_xboole_0(k10_yellow_6(sK0,sK3)) ),
    inference(resolution,[],[f161,f135])).

fof(f161,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ v1_xboole_0(k10_yellow_6(sK0,sK3)) ),
    inference(resolution,[],[f146,f111])).

fof(f111,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK3))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f80])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t7_boole)).

fof(f822,plain,(
    ! [X4] :
      ( ~ r1_waybel_0(sK0,sK3,sK1)
      | ~ l1_waybel_0(sK3,sK0)
      | ~ v3_yellow_6(sK3,sK0)
      | ~ v7_waybel_0(sK3)
      | ~ v4_orders_2(sK3)
      | v2_struct_0(sK3)
      | v1_xboole_0(k10_yellow_6(sK0,sK3))
      | ~ r3_waybel_9(sK0,X4,sK2)
      | ~ r1_waybel_0(sK0,X4,sK1)
      | ~ l1_waybel_0(X4,sK0)
      | ~ v7_waybel_0(X4)
      | ~ v4_orders_2(X4)
      | v2_struct_0(X4)
      | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f372,f346])).

fof(f346,plain,
    ( m1_subset_1(sK2,k10_yellow_6(sK0,sK3))
    | m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f175,f135])).

fof(f175,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | m1_subset_1(sK2,k10_yellow_6(sK0,sK3)) ),
    inference(resolution,[],[f135,f111])).

fof(f372,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK2,k10_yellow_6(sK0,X10))
      | ~ r1_waybel_0(sK0,X10,sK1)
      | ~ l1_waybel_0(X10,sK0)
      | ~ v3_yellow_6(X10,sK0)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | v1_xboole_0(k10_yellow_6(sK0,X10))
      | ~ r3_waybel_9(sK0,X11,sK2)
      | ~ r1_waybel_0(sK0,X11,sK1)
      | ~ l1_waybel_0(X11,sK0)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11) ) ),
    inference(subsumption_resolution,[],[f371,f100])).

fof(f371,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK2,k10_yellow_6(sK0,X10))
      | ~ r1_waybel_0(sK0,X10,sK1)
      | ~ l1_waybel_0(X10,sK0)
      | ~ v3_yellow_6(X10,sK0)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | v1_xboole_0(k10_yellow_6(sK0,X10))
      | ~ r3_waybel_9(sK0,X11,sK2)
      | ~ r1_waybel_0(sK0,X11,sK1)
      | ~ l1_waybel_0(X11,sK0)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f370,f101])).

fof(f370,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK2,k10_yellow_6(sK0,X10))
      | ~ r1_waybel_0(sK0,X10,sK1)
      | ~ l1_waybel_0(X10,sK0)
      | ~ v3_yellow_6(X10,sK0)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | v1_xboole_0(k10_yellow_6(sK0,X10))
      | ~ r3_waybel_9(sK0,X11,sK2)
      | ~ r1_waybel_0(sK0,X11,sK1)
      | ~ l1_waybel_0(X11,sK0)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f369,f102])).

fof(f369,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK2,k10_yellow_6(sK0,X10))
      | ~ r1_waybel_0(sK0,X10,sK1)
      | ~ l1_waybel_0(X10,sK0)
      | ~ v3_yellow_6(X10,sK0)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | v1_xboole_0(k10_yellow_6(sK0,X10))
      | ~ r3_waybel_9(sK0,X11,sK2)
      | ~ r1_waybel_0(sK0,X11,sK1)
      | ~ l1_waybel_0(X11,sK0)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f368,f103])).

fof(f368,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK2,k10_yellow_6(sK0,X10))
      | ~ r1_waybel_0(sK0,X10,sK1)
      | ~ l1_waybel_0(X10,sK0)
      | ~ v3_yellow_6(X10,sK0)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | v1_xboole_0(k10_yellow_6(sK0,X10))
      | ~ r3_waybel_9(sK0,X11,sK2)
      | ~ r1_waybel_0(sK0,X11,sK1)
      | ~ l1_waybel_0(X11,sK0)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f366,f104])).

fof(f366,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK2,k10_yellow_6(sK0,X10))
      | ~ r1_waybel_0(sK0,X10,sK1)
      | ~ l1_waybel_0(X10,sK0)
      | ~ v3_yellow_6(X10,sK0)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | v1_xboole_0(k10_yellow_6(sK0,X10))
      | ~ r3_waybel_9(sK0,X11,sK2)
      | ~ r1_waybel_0(sK0,X11,sK1)
      | ~ l1_waybel_0(X11,sK0)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f182,f126])).

fof(f126,plain,(
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
    inference(cnf_transformation,[],[f86])).

fof(f182,plain,(
    ! [X6] :
      ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,k10_yellow_6(sK0,X6))
      | ~ r1_waybel_0(sK0,X6,sK1)
      | ~ l1_waybel_0(X6,sK0)
      | ~ v3_yellow_6(X6,sK0)
      | ~ v7_waybel_0(X6)
      | ~ v4_orders_2(X6)
      | v2_struct_0(X6)
      | v1_xboole_0(k10_yellow_6(sK0,X6)) ) ),
    inference(resolution,[],[f136,f112])).

fof(f112,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X3))
      | ~ r1_waybel_0(sK0,X3,sK1)
      | ~ l1_waybel_0(X3,sK0)
      | ~ v3_yellow_6(X3,sK0)
      | ~ v7_waybel_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t2_subset)).

fof(f1209,plain,(
    ! [X14] :
      ( ~ r1_waybel_0(sK0,X14,sK1)
      | ~ l1_waybel_0(X14,sK0)
      | ~ v7_waybel_0(X14)
      | ~ v4_orders_2(X14)
      | v2_struct_0(X14)
      | v2_struct_0(sK6(sK0,X14,sK2))
      | ~ r3_waybel_9(sK0,X14,sK2)
      | ~ m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1203,f624])).

fof(f624,plain,(
    ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f623,f155])).

fof(f155,plain,
    ( ~ v1_xboole_0(k2_pre_topc(sK0,sK1))
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(resolution,[],[f146,f110])).

fof(f623,plain,
    ( ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f622,f156])).

fof(f156,plain,
    ( ~ v1_xboole_0(k2_pre_topc(sK0,sK1))
    | l1_waybel_0(sK3,sK0) ),
    inference(resolution,[],[f146,f109])).

fof(f622,plain,
    ( ~ l1_waybel_0(sK3,sK0)
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f621,f158])).

fof(f158,plain,
    ( ~ v1_xboole_0(k2_pre_topc(sK0,sK1))
    | v7_waybel_0(sK3) ),
    inference(resolution,[],[f146,f107])).

fof(f621,plain,
    ( ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f620,f159])).

fof(f159,plain,
    ( ~ v1_xboole_0(k2_pre_topc(sK0,sK1))
    | v4_orders_2(sK3) ),
    inference(resolution,[],[f146,f106])).

fof(f620,plain,
    ( ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f619,f160])).

fof(f160,plain,
    ( ~ v1_xboole_0(k2_pre_topc(sK0,sK1))
    | ~ v2_struct_0(sK3) ),
    inference(resolution,[],[f146,f105])).

fof(f619,plain,
    ( ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f618,f104])).

fof(f618,plain,
    ( ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f611])).

fof(f611,plain,
    ( ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1))
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f558,f302])).

fof(f302,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f283,f146])).

fof(f283,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | r3_waybel_9(sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f282,f105])).

fof(f282,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | v2_struct_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f281,f106])).

fof(f281,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f280,f107])).

fof(f280,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f279,f109])).

fof(f279,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f278,f100])).

fof(f278,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f277,f101])).

fof(f277,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f276,f102])).

fof(f276,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f272,f104])).

fof(f272,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK3,sK0)
    | ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f129,f111])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t29_waybel_9)).

fof(f558,plain,(
    ! [X12,X13] :
      ( ~ r3_waybel_9(sK0,X12,X13)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ r1_waybel_0(sK0,X12,sK1)
      | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f557,f100])).

fof(f557,plain,(
    ! [X12,X13] :
      ( ~ r1_waybel_0(sK0,X12,sK1)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X12,X13)
      | v2_struct_0(sK0)
      | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f556,f101])).

fof(f556,plain,(
    ! [X12,X13] :
      ( ~ r1_waybel_0(sK0,X12,sK1)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X12,X13)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f551,f102])).

fof(f551,plain,(
    ! [X12,X13] :
      ( ~ r1_waybel_0(sK0,X12,sK1)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ m1_subset_1(X13,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X12,X13)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v1_xboole_0(k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f331,f103])).

fof(f331,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ r1_waybel_0(X12,X13,X15)
      | ~ l1_waybel_0(X13,X12)
      | ~ v7_waybel_0(X13)
      | ~ v4_orders_2(X13)
      | v2_struct_0(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ r3_waybel_9(X12,X13,X14)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12)
      | v2_struct_0(X12)
      | ~ v1_xboole_0(k2_pre_topc(X12,X15)) ) ),
    inference(resolution,[],[f126,f146])).

fof(f1203,plain,(
    ! [X14] :
      ( ~ r1_waybel_0(sK0,X14,sK1)
      | ~ l1_waybel_0(X14,sK0)
      | ~ v7_waybel_0(X14)
      | ~ v4_orders_2(X14)
      | v2_struct_0(X14)
      | v2_struct_0(sK6(sK0,X14,sK2))
      | ~ r3_waybel_9(sK0,X14,sK2)
      | v1_xboole_0(k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f1169,f136])).

fof(f1169,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r3_waybel_9(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f1168,f100])).

fof(f1168,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1167,f101])).

fof(f1167,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1166,f102])).

fof(f1166,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1165,f104])).

fof(f1165,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1164])).

fof(f1164,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2) ) ),
    inference(resolution,[],[f1160,f297])).

fof(f297,plain,(
    ! [X12,X10,X11] :
      ( v4_orders_2(sK6(X10,X11,X12))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | ~ r3_waybel_9(X10,X11,X12) ) ),
    inference(subsumption_resolution,[],[f290,f117])).

fof(f290,plain,(
    ! [X12,X10,X11] :
      ( ~ r3_waybel_9(X10,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | v4_orders_2(sK6(X10,X11,X12))
      | ~ l1_struct_0(X10) ) ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,(
    ! [X12,X10,X11] :
      ( ~ r3_waybel_9(X10,X11,X12)
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | v2_struct_0(X10)
      | v4_orders_2(sK6(X10,X11,X12))
      | ~ l1_waybel_0(X11,X10)
      | ~ v7_waybel_0(X11)
      | ~ v4_orders_2(X11)
      | v2_struct_0(X11)
      | ~ l1_struct_0(X10)
      | v2_struct_0(X10) ) ),
    inference(resolution,[],[f130,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1160,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK6(sK0,X0,sK2))
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1159,f100])).

fof(f1159,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1158,f101])).

fof(f1158,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1157,f102])).

fof(f1157,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1156,f104])).

fof(f1156,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1155])).

fof(f1155,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2) ) ),
    inference(resolution,[],[f1149,f296])).

fof(f296,plain,(
    ! [X8,X7,X9] :
      ( v7_waybel_0(sK6(X7,X8,X9))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | ~ r3_waybel_9(X7,X8,X9) ) ),
    inference(subsumption_resolution,[],[f291,f117])).

fof(f291,plain,(
    ! [X8,X7,X9] :
      ( ~ r3_waybel_9(X7,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | v7_waybel_0(sK6(X7,X8,X9))
      | ~ l1_struct_0(X7) ) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,(
    ! [X8,X7,X9] :
      ( ~ r3_waybel_9(X7,X8,X9)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | v7_waybel_0(sK6(X7,X8,X9))
      | ~ l1_waybel_0(X8,X7)
      | ~ v7_waybel_0(X8)
      | ~ v4_orders_2(X8)
      | v2_struct_0(X8)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f130,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f1149,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1148,f104])).

fof(f1148,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1147,f100])).

fof(f1147,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1146,f101])).

fof(f1146,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1145,f102])).

fof(f1145,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1142])).

fof(f1142,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f868,f514])).

fof(f514,plain,(
    ! [X2,X0,X1] :
      ( v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f513,f298])).

fof(f513,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f512,f297])).

fof(f512,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f511,f296])).

fof(f511,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f510,f295])).

fof(f295,plain,(
    ! [X6,X4,X5] :
      ( l1_waybel_0(sK6(X4,X5,X6),X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | ~ r3_waybel_9(X4,X5,X6) ) ),
    inference(subsumption_resolution,[],[f292,f117])).

fof(f292,plain,(
    ! [X6,X4,X5] :
      ( ~ r3_waybel_9(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | l1_waybel_0(sK6(X4,X5,X6),X4)
      | ~ l1_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X6,X4,X5] :
      ( ~ r3_waybel_9(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | l1_waybel_0(sK6(X4,X5,X6),X4)
      | ~ l1_waybel_0(X5,X4)
      | ~ v7_waybel_0(X5)
      | ~ v4_orders_2(X5)
      | v2_struct_0(X5)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f130,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f510,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f509,f152])).

fof(f152,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f113,f114])).

fof(f114,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',d2_xboole_0)).

fof(f113,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',dt_o_0_0_xboole_0)).

fof(f509,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f508])).

fof(f508,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | v3_yellow_6(sK6(X0,X1,X2),X0)
      | ~ l1_waybel_0(sK6(X0,X1,X2),X0)
      | ~ v7_waybel_0(sK6(X0,X1,X2))
      | ~ v4_orders_2(sK6(X0,X1,X2))
      | v2_struct_0(sK6(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f311,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k10_yellow_6(X0,X1) = k1_xboole_0
      | v3_yellow_6(X1,X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',d19_yellow_6)).

fof(f311,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_xboole_0(k10_yellow_6(X9,sK6(X9,X10,X11)))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ l1_waybel_0(X10,X9)
      | ~ v7_waybel_0(X10)
      | ~ v4_orders_2(X10)
      | v2_struct_0(X10)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ r3_waybel_9(X9,X10,X11) ) ),
    inference(resolution,[],[f131,f146])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK6(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f868,plain,(
    ! [X0] :
      ( ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f867,f100])).

fof(f867,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f866,f101])).

fof(f866,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f865,f102])).

fof(f865,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f864,f104])).

fof(f864,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f863])).

fof(f863,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2) ) ),
    inference(resolution,[],[f546,f295])).

fof(f546,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f545,f100])).

fof(f545,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(sK6(sK0,X0,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f544,f101])).

fof(f544,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(sK6(sK0,X0,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f543,f102])).

fof(f543,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(sK6(sK0,X0,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f542,f104])).

fof(f542,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(sK6(sK0,X0,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f541])).

fof(f541,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ r1_waybel_0(sK0,X0,sK1)
      | ~ l1_waybel_0(X0,sK0)
      | ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(sK0,X0,sK2)
      | ~ l1_waybel_0(sK6(sK0,X0,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X0,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X0,sK2))
      | ~ v4_orders_2(sK6(sK0,X0,sK2))
      | v2_struct_0(sK6(sK0,X0,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f294,f323])).

fof(f323,plain,(
    ! [X12] :
      ( ~ r1_waybel_0(sK0,sK6(sK0,X12,sK2),sK1)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ r3_waybel_9(sK0,X12,sK2)
      | ~ l1_waybel_0(sK6(sK0,X12,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X12,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X12,sK2))
      | ~ v4_orders_2(sK6(sK0,X12,sK2))
      | v2_struct_0(sK6(sK0,X12,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f322,f100])).

fof(f322,plain,(
    ! [X12] :
      ( ~ r3_waybel_9(sK0,X12,sK2)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,sK6(sK0,X12,sK2),sK1)
      | ~ l1_waybel_0(sK6(sK0,X12,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X12,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X12,sK2))
      | ~ v4_orders_2(sK6(sK0,X12,sK2))
      | v2_struct_0(sK6(sK0,X12,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f321,f101])).

fof(f321,plain,(
    ! [X12] :
      ( ~ r3_waybel_9(sK0,X12,sK2)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,sK6(sK0,X12,sK2),sK1)
      | ~ l1_waybel_0(sK6(sK0,X12,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X12,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X12,sK2))
      | ~ v4_orders_2(sK6(sK0,X12,sK2))
      | v2_struct_0(sK6(sK0,X12,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f320,f102])).

fof(f320,plain,(
    ! [X12] :
      ( ~ r3_waybel_9(sK0,X12,sK2)
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,sK6(sK0,X12,sK2),sK1)
      | ~ l1_waybel_0(sK6(sK0,X12,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X12,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X12,sK2))
      | ~ v4_orders_2(sK6(sK0,X12,sK2))
      | v2_struct_0(sK6(sK0,X12,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f312,f104])).

fof(f312,plain,(
    ! [X12] :
      ( ~ r3_waybel_9(sK0,X12,sK2)
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(X12,sK0)
      | ~ v7_waybel_0(X12)
      | ~ v4_orders_2(X12)
      | v2_struct_0(X12)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,sK6(sK0,X12,sK2),sK1)
      | ~ l1_waybel_0(sK6(sK0,X12,sK2),sK0)
      | ~ v3_yellow_6(sK6(sK0,X12,sK2),sK0)
      | ~ v7_waybel_0(sK6(sK0,X12,sK2))
      | ~ v4_orders_2(sK6(sK0,X12,sK2))
      | v2_struct_0(sK6(sK0,X12,sK2))
      | ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f131,f112])).

fof(f294,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,sK6(X0,X1,X2),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ r1_waybel_0(X0,X1,X3) ) ),
    inference(subsumption_resolution,[],[f293,f117])).

fof(f293,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(X0,sK6(X0,X1,X2),X3)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f284])).

fof(f284,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(X0,sK6(X0,X1,X2),X3)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f130,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_yellow_6(X3,X0,X2)
      | r1_waybel_0(X0,X3,X1)
      | ~ r1_waybel_0(X0,X2,X1)
      | ~ l1_waybel_0(X2,X0)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t24_yellow19.p',t21_yellow19)).

fof(f1557,plain,(
    ~ l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f1556,f1479])).

fof(f1479,plain,(
    r1_waybel_0(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f1465,f258])).

fof(f258,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f257,f100])).

fof(f257,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f256,f101])).

fof(f256,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f255,f102])).

fof(f255,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f254,f103])).

fof(f254,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(subsumption_resolution,[],[f224,f104])).

fof(f224,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(resolution,[],[f120,f110])).

fof(f1465,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | r1_waybel_0(sK0,sK3,sK1) ),
    inference(resolution,[],[f1454,f110])).

fof(f1556,plain,
    ( ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f1555,f1474])).

fof(f1474,plain,(
    ~ v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1460,f233])).

fof(f233,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f232,f100])).

fof(f232,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f231,f101])).

fof(f231,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f230,f102])).

fof(f230,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f229,f103])).

fof(f229,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f219,f104])).

fof(f219,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3) ),
    inference(resolution,[],[f120,f105])).

fof(f1460,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_struct_0(sK3) ),
    inference(resolution,[],[f1454,f105])).

fof(f1555,plain,
    ( v2_struct_0(sK3)
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f1554,f1475])).

fof(f1475,plain,(
    v4_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f1461,f238])).

fof(f238,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v4_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f237,f100])).

fof(f237,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | v4_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f236,f101])).

fof(f236,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v4_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f235,f102])).

fof(f235,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v4_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f234,f103])).

fof(f234,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v4_orders_2(sK3) ),
    inference(subsumption_resolution,[],[f220,f104])).

fof(f220,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v4_orders_2(sK3) ),
    inference(resolution,[],[f120,f106])).

fof(f1461,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | v4_orders_2(sK3) ),
    inference(resolution,[],[f1454,f106])).

fof(f1554,plain,
    ( ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ l1_waybel_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f1550,f1476])).

fof(f1476,plain,(
    v7_waybel_0(sK3) ),
    inference(subsumption_resolution,[],[f1462,f243])).

fof(f243,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v7_waybel_0(sK3) ),
    inference(subsumption_resolution,[],[f242,f100])).

fof(f242,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | v7_waybel_0(sK3) ),
    inference(subsumption_resolution,[],[f241,f101])).

fof(f241,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_waybel_0(sK3) ),
    inference(subsumption_resolution,[],[f240,f102])).

fof(f240,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_waybel_0(sK3) ),
    inference(subsumption_resolution,[],[f239,f103])).

fof(f239,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_waybel_0(sK3) ),
    inference(subsumption_resolution,[],[f221,f104])).

fof(f221,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_waybel_0(sK3) ),
    inference(resolution,[],[f120,f107])).

fof(f1462,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | v7_waybel_0(sK3) ),
    inference(resolution,[],[f1454,f107])).

fof(f1550,plain,
    ( ~ v7_waybel_0(sK3)
    | ~ v4_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ r1_waybel_0(sK0,sK3,sK1)
    | ~ l1_waybel_0(sK3,sK0) ),
    inference(resolution,[],[f1483,f1218])).

fof(f1483,plain,(
    r3_waybel_9(sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f1469,f307])).

fof(f307,plain,
    ( ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK3,sK2) ),
    inference(subsumption_resolution,[],[f306,f100])).

fof(f306,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f305,f101])).

fof(f305,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f304,f102])).

fof(f304,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f303,f103])).

fof(f303,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f299,f104])).

fof(f299,plain,
    ( r3_waybel_9(sK0,sK3,sK2)
    | ~ v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f283,f120])).

fof(f1469,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | r3_waybel_9(sK0,sK3,sK2) ),
    inference(resolution,[],[f1454,f283])).
%------------------------------------------------------------------------------
