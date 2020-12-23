%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:39 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  106 (1013 expanded)
%              Number of leaves         :   17 ( 270 expanded)
%              Depth                    :   35
%              Number of atoms          :  490 (5566 expanded)
%              Number of equality atoms :   15 (  65 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f303,f348])).

fof(f348,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl7_1 ),
    inference(resolution,[],[f339,f102])).

fof(f102,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_1
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f339,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | ~ spl7_1 ),
    inference(resolution,[],[f324,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f324,plain,
    ( ! [X0] : r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,u1_struct_0(sK1))),X0)
    | ~ spl7_1 ),
    inference(resolution,[],[f323,f224])).

fof(f224,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7) ) ),
    inference(subsumption_resolution,[],[f223,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f223,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f222,f50])).

fof(f50,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f222,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f221,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f221,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f212,f52])).

fof(f52,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f212,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK1))
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f208,f58])).

fof(f58,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f208,plain,(
    ! [X0] : r2_waybel_0(sK0,sK1,X0) ),
    inference(subsumption_resolution,[],[f207,f53])).

fof(f53,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f207,plain,(
    ! [X0] :
      ( r2_waybel_0(sK0,sK1,X0)
      | r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X0] :
      ( r2_waybel_0(sK0,sK1,X0)
      | r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f175,f117])).

fof(f117,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2)
      | r1_waybel_0(sK0,sK1,X2)
      | r2_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f116,f49])).

fof(f116,plain,(
    ! [X2,X1] :
      ( r2_waybel_0(sK0,sK1,X1)
      | r1_waybel_0(sK0,sK1,X2)
      | ~ r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,(
    ! [X2,X1] :
      ( r2_waybel_0(sK0,sK1,X1)
      | r1_waybel_0(sK0,sK1,X2)
      | ~ r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f51])).

fof(f114,plain,(
    ! [X2,X1] :
      ( r2_waybel_0(sK0,sK1,X1)
      | r1_waybel_0(sK0,sK1,X2)
      | ~ r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f52])).

fof(f113,plain,(
    ! [X2,X1] :
      ( r2_waybel_0(sK0,sK1,X1)
      | r1_waybel_0(sK0,sK1,X2)
      | ~ r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2)
      | ~ l1_waybel_0(sK1,sK0)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(f96,plain,(
    ! [X1] :
      ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f95,plain,(
    ! [X1] :
      ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,sK1,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f50])).

fof(f94,plain,(
    ! [X1] :
      ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,sK1,X1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f51])).

fof(f90,plain,(
    ! [X1] :
      ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,sK1,X1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f52,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f175,plain,(
    ! [X1] :
      ( r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
      | r2_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f171,f53])).

fof(f171,plain,(
    ! [X1] :
      ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      | r2_waybel_0(sK0,sK1,X1)
      | r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f126,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f126,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),X1),u1_struct_0(sK0))
      | r1_waybel_0(sK0,sK1,X1)
      | r2_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f125,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f74,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

% (5462)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

% (5445)Refutation not found, incomplete strategy% (5445)------------------------------
% (5445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5445)Termination reason: Refutation not found, incomplete strategy

% (5445)Memory used [KB]: 10618
% (5445)Time elapsed: 0.191 s
% (5445)------------------------------
% (5445)------------------------------
fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X1),X0),k6_subset_1(u1_struct_0(sK0),X1))
      | r2_waybel_0(sK0,sK1,X1)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f323,plain,
    ( m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_1 ),
    inference(resolution,[],[f320,f102])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | m1_subset_1(u1_struct_0(sK1),X0) )
    | ~ spl7_1 ),
    inference(resolution,[],[f102,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f303,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f278,f277])).

fof(f277,plain,
    ( ! [X2,X3] : r2_hidden(sK4(k6_subset_1(X2,X3)),X2)
    | spl7_1 ),
    inference(resolution,[],[f270,f88])).

fof(f270,plain,
    ( ! [X0] : r2_hidden(sK4(X0),X0)
    | spl7_1 ),
    inference(resolution,[],[f266,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f266,plain,
    ( ! [X1] : ~ v1_xboole_0(X1)
    | spl7_1 ),
    inference(resolution,[],[f264,f63])).

fof(f264,plain,
    ( ! [X9] : r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X9,sK4(u1_struct_0(sK1)))),X9)
    | spl7_1 ),
    inference(resolution,[],[f224,f120])).

fof(f120,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f118,f101])).

fof(f101,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f118,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | spl7_1 ),
    inference(resolution,[],[f111,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl7_1 ),
    inference(resolution,[],[f101,f64])).

fof(f278,plain,
    ( ! [X4,X5] : ~ r2_hidden(sK4(k6_subset_1(X4,X5)),X5)
    | spl7_1 ),
    inference(resolution,[],[f270,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_subset_1(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f75,f65])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:39:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (5436)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.56  % (5458)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.56  % (5439)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.56  % (5450)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.57/0.57  % (5444)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.57/0.57  % (5441)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.57/0.57  % (5442)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.57/0.58  % (5444)Refutation not found, incomplete strategy% (5444)------------------------------
% 1.57/0.58  % (5444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (5444)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (5444)Memory used [KB]: 10618
% 1.57/0.58  % (5444)Time elapsed: 0.004 s
% 1.57/0.58  % (5444)------------------------------
% 1.57/0.58  % (5444)------------------------------
% 1.57/0.58  % (5437)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.57/0.59  % (5440)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.57/0.59  % (5457)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.57/0.59  % (5454)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.57/0.60  % (5464)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.60  % (5456)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.57/0.60  % (5449)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.57/0.60  % (5463)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.57/0.60  % (5445)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.57/0.60  % (5447)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.57/0.61  % (5446)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.57/0.61  % (5438)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.57/0.61  % (5459)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.61  % (5455)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.57/0.61  % (5452)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.57/0.61  % (5443)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.57/0.61  % (5448)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.61  % (5461)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.57/0.61  % (5435)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.57/0.61  % (5452)Refutation not found, incomplete strategy% (5452)------------------------------
% 1.57/0.61  % (5452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (5435)Refutation not found, incomplete strategy% (5435)------------------------------
% 1.57/0.61  % (5435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.61  % (5435)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.61  
% 1.57/0.61  % (5435)Memory used [KB]: 1663
% 1.57/0.61  % (5435)Time elapsed: 0.003 s
% 1.57/0.61  % (5435)------------------------------
% 1.57/0.61  % (5435)------------------------------
% 1.57/0.62  % (5443)Refutation found. Thanks to Tanya!
% 1.57/0.62  % SZS status Theorem for theBenchmark
% 1.57/0.62  % (5452)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (5452)Memory used [KB]: 10618
% 1.57/0.62  % (5452)Time elapsed: 0.184 s
% 1.57/0.62  % (5452)------------------------------
% 1.57/0.62  % (5452)------------------------------
% 1.57/0.62  % (5453)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.57/0.62  % (5446)Refutation not found, incomplete strategy% (5446)------------------------------
% 1.57/0.62  % (5446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (5446)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (5446)Memory used [KB]: 10618
% 1.57/0.62  % (5446)Time elapsed: 0.191 s
% 1.57/0.62  % (5446)------------------------------
% 1.57/0.62  % (5446)------------------------------
% 1.57/0.62  % (5451)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.57/0.62  % SZS output start Proof for theBenchmark
% 1.57/0.62  fof(f349,plain,(
% 1.57/0.62    $false),
% 1.57/0.62    inference(avatar_sat_refutation,[],[f303,f348])).
% 1.57/0.62  fof(f348,plain,(
% 1.57/0.62    ~spl7_1),
% 1.57/0.62    inference(avatar_contradiction_clause,[],[f346])).
% 1.57/0.62  fof(f346,plain,(
% 1.57/0.62    $false | ~spl7_1),
% 1.57/0.62    inference(resolution,[],[f339,f102])).
% 1.57/0.62  fof(f102,plain,(
% 1.57/0.62    v1_xboole_0(u1_struct_0(sK1)) | ~spl7_1),
% 1.57/0.62    inference(avatar_component_clause,[],[f100])).
% 1.57/0.62  fof(f100,plain,(
% 1.57/0.62    spl7_1 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.57/0.62    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.57/0.62  fof(f339,plain,(
% 1.57/0.62    ( ! [X1] : (~v1_xboole_0(X1)) ) | ~spl7_1),
% 1.57/0.62    inference(resolution,[],[f324,f63])).
% 1.57/0.62  fof(f63,plain,(
% 1.57/0.62    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f40])).
% 1.57/0.62  fof(f40,plain,(
% 1.57/0.62    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.57/0.62  fof(f39,plain,(
% 1.57/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f38,plain,(
% 1.57/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.62    inference(rectify,[],[f37])).
% 1.57/0.62  fof(f37,plain,(
% 1.57/0.62    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.57/0.62    inference(nnf_transformation,[],[f1])).
% 1.57/0.62  fof(f1,axiom,(
% 1.57/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.57/0.62  fof(f324,plain,(
% 1.57/0.62    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,u1_struct_0(sK1))),X0)) ) | ~spl7_1),
% 1.57/0.62    inference(resolution,[],[f323,f224])).
% 1.57/0.62  fof(f224,plain,(
% 1.57/0.62    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f223,f49])).
% 1.57/0.62  fof(f49,plain,(
% 1.57/0.62    ~v2_struct_0(sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f30])).
% 1.57/0.62  fof(f30,plain,(
% 1.57/0.62    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f29,f28])).
% 1.57/0.62  fof(f28,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f29,plain,(
% 1.57/0.62    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f17,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.57/0.62    inference(flattening,[],[f16])).
% 1.57/0.62  fof(f16,plain,(
% 1.57/0.62    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f15])).
% 1.57/0.62  fof(f15,plain,(
% 1.57/0.62    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.57/0.62    inference(pure_predicate_removal,[],[f14])).
% 1.57/0.62  fof(f14,plain,(
% 1.57/0.62    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.57/0.62    inference(pure_predicate_removal,[],[f12])).
% 1.57/0.62  fof(f12,negated_conjecture,(
% 1.57/0.62    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.57/0.62    inference(negated_conjecture,[],[f11])).
% 1.57/0.62  fof(f11,conjecture,(
% 1.57/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 1.57/0.62  fof(f223,plain,(
% 1.57/0.62    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f222,f50])).
% 1.57/0.62  fof(f50,plain,(
% 1.57/0.62    l1_struct_0(sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f30])).
% 1.57/0.62  fof(f222,plain,(
% 1.57/0.62    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f221,f51])).
% 1.57/0.62  fof(f51,plain,(
% 1.57/0.62    ~v2_struct_0(sK1)),
% 1.57/0.62    inference(cnf_transformation,[],[f30])).
% 1.57/0.62  fof(f221,plain,(
% 1.57/0.62    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f212,f52])).
% 1.57/0.62  fof(f52,plain,(
% 1.57/0.62    l1_waybel_0(sK1,sK0)),
% 1.57/0.62    inference(cnf_transformation,[],[f30])).
% 1.57/0.62  fof(f212,plain,(
% 1.57/0.62    ( ! [X6,X7] : (~m1_subset_1(X6,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X7,X6)),X7) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(resolution,[],[f208,f58])).
% 1.57/0.62  fof(f58,plain,(
% 1.57/0.62    ( ! [X2,X0,X5,X1] : (~r2_waybel_0(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f36])).
% 1.57/0.62  fof(f36,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f33,f35,f34])).
% 1.57/0.62  fof(f34,plain,(
% 1.57/0.62    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f35,plain,(
% 1.57/0.62    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f33,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(rectify,[],[f32])).
% 1.57/0.62  fof(f32,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(nnf_transformation,[],[f21])).
% 1.57/0.62  fof(f21,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(flattening,[],[f20])).
% 1.57/0.62  fof(f20,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f8])).
% 1.57/0.62  fof(f8,axiom,(
% 1.57/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 1.57/0.62  fof(f208,plain,(
% 1.57/0.62    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f207,f53])).
% 1.57/0.62  fof(f53,plain,(
% 1.57/0.62    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 1.57/0.62    inference(cnf_transformation,[],[f30])).
% 1.57/0.62  fof(f207,plain,(
% 1.57/0.62    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0) | r1_waybel_0(sK0,sK1,u1_struct_0(sK0))) )),
% 1.57/0.62    inference(duplicate_literal_removal,[],[f206])).
% 1.57/0.62  fof(f206,plain,(
% 1.57/0.62    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0) | r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.57/0.62    inference(resolution,[],[f175,f117])).
% 1.57/0.62  fof(f117,plain,(
% 1.57/0.62    ( ! [X2,X1] : (~r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2) | r1_waybel_0(sK0,sK1,X2) | r2_waybel_0(sK0,sK1,X1)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f116,f49])).
% 1.57/0.62  fof(f116,plain,(
% 1.57/0.62    ( ! [X2,X1] : (r2_waybel_0(sK0,sK1,X1) | r1_waybel_0(sK0,sK1,X2) | ~r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f115,f50])).
% 1.57/0.62  fof(f115,plain,(
% 1.57/0.62    ( ! [X2,X1] : (r2_waybel_0(sK0,sK1,X1) | r1_waybel_0(sK0,sK1,X2) | ~r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f114,f51])).
% 1.57/0.62  fof(f114,plain,(
% 1.57/0.62    ( ! [X2,X1] : (r2_waybel_0(sK0,sK1,X1) | r1_waybel_0(sK0,sK1,X2) | ~r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f113,f52])).
% 1.57/0.62  fof(f113,plain,(
% 1.57/0.62    ( ! [X2,X1] : (r2_waybel_0(sK0,sK1,X1) | r1_waybel_0(sK0,sK1,X2) | ~r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),X2) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(resolution,[],[f96,f61])).
% 1.57/0.62  fof(f61,plain,(
% 1.57/0.62    ( ! [X2,X0,X3,X1] : (~r1_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,X3) | ~r1_tarski(X2,X3) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f23])).
% 1.57/0.62  fof(f23,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(flattening,[],[f22])).
% 1.57/0.62  fof(f22,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f10])).
% 1.57/0.62  fof(f10,axiom,(
% 1.57/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).
% 1.57/0.62  fof(f96,plain,(
% 1.57/0.62    ( ! [X1] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,sK1,X1)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f95,f49])).
% 1.57/0.62  fof(f95,plain,(
% 1.57/0.62    ( ! [X1] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,sK1,X1) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f94,f50])).
% 1.57/0.62  fof(f94,plain,(
% 1.57/0.62    ( ! [X1] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,sK1,X1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f90,f51])).
% 1.57/0.62  fof(f90,plain,(
% 1.57/0.62    ( ! [X1] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,sK1,X1) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 1.57/0.62    inference(resolution,[],[f52,f55])).
% 1.57/0.62  fof(f55,plain,(
% 1.57/0.62    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f31])).
% 1.57/0.62  fof(f31,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(nnf_transformation,[],[f19])).
% 1.57/0.62  fof(f19,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.57/0.62    inference(flattening,[],[f18])).
% 1.57/0.62  fof(f18,plain,(
% 1.57/0.62    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f9])).
% 1.57/0.62  fof(f9,axiom,(
% 1.57/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 1.57/0.62  fof(f175,plain,(
% 1.57/0.62    ( ! [X1] : (r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | r2_waybel_0(sK0,sK1,X1)) )),
% 1.57/0.62    inference(subsumption_resolution,[],[f171,f53])).
% 1.57/0.62  fof(f171,plain,(
% 1.57/0.62    ( ! [X1] : (r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_waybel_0(sK0,sK1,X1) | r1_tarski(k6_subset_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))) )),
% 1.57/0.62    inference(resolution,[],[f126,f73])).
% 1.57/0.62  fof(f73,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f43])).
% 1.57/0.62  fof(f43,plain,(
% 1.57/0.62    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f42])).
% 1.57/0.62  fof(f42,plain,(
% 1.57/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f27,plain,(
% 1.57/0.62    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f13])).
% 1.57/0.62  fof(f13,plain,(
% 1.57/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.57/0.62    inference(unused_predicate_definition_removal,[],[f2])).
% 1.57/0.62  fof(f2,axiom,(
% 1.57/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.57/0.62  fof(f126,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X0),X1),u1_struct_0(sK0)) | r1_waybel_0(sK0,sK1,X1) | r2_waybel_0(sK0,sK1,X0)) )),
% 1.57/0.62    inference(resolution,[],[f125,f88])).
% 1.57/0.62  fof(f88,plain,(
% 1.57/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_subset_1(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.57/0.62    inference(equality_resolution,[],[f85])).
% 1.57/0.62  fof(f85,plain,(
% 1.57/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.57/0.62    inference(definition_unfolding,[],[f74,f65])).
% 1.57/0.62  fof(f65,plain,(
% 1.57/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f6])).
% 1.57/0.62  % (5462)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.57/0.62  fof(f6,axiom,(
% 1.57/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.57/0.62  fof(f74,plain,(
% 1.57/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.62    inference(cnf_transformation,[],[f48])).
% 1.57/0.62  fof(f48,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f46,f47])).
% 1.57/0.62  fof(f47,plain,(
% 1.57/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.57/0.62    introduced(choice_axiom,[])).
% 1.57/0.62  fof(f46,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(rectify,[],[f45])).
% 1.57/0.62  fof(f45,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(flattening,[],[f44])).
% 1.57/0.62  fof(f44,plain,(
% 1.57/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.57/0.62    inference(nnf_transformation,[],[f3])).
% 1.57/0.62  fof(f3,axiom,(
% 1.57/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.57/0.62  % (5445)Refutation not found, incomplete strategy% (5445)------------------------------
% 1.57/0.62  % (5445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.62  % (5445)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.62  
% 1.57/0.62  % (5445)Memory used [KB]: 10618
% 1.57/0.62  % (5445)Time elapsed: 0.191 s
% 1.57/0.62  % (5445)------------------------------
% 1.57/0.62  % (5445)------------------------------
% 1.57/0.62  fof(f125,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r2_hidden(sK5(k6_subset_1(u1_struct_0(sK0),X1),X0),k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,sK1,X1) | r1_waybel_0(sK0,sK1,X0)) )),
% 1.57/0.62    inference(resolution,[],[f117,f72])).
% 1.57/0.62  fof(f72,plain,(
% 1.57/0.62    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f43])).
% 1.57/0.62  fof(f323,plain,(
% 1.57/0.62    m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) | ~spl7_1),
% 1.57/0.62    inference(resolution,[],[f320,f102])).
% 1.57/0.62  fof(f320,plain,(
% 1.57/0.62    ( ! [X0] : (~v1_xboole_0(X0) | m1_subset_1(u1_struct_0(sK1),X0)) ) | ~spl7_1),
% 1.57/0.62    inference(resolution,[],[f102,f69])).
% 1.57/0.62  fof(f69,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~v1_xboole_0(X1) | m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f41])).
% 1.57/0.62  fof(f41,plain,(
% 1.57/0.62    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.57/0.62    inference(nnf_transformation,[],[f24])).
% 1.57/0.62  fof(f24,plain,(
% 1.57/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.57/0.62    inference(ennf_transformation,[],[f4])).
% 1.57/0.62  fof(f4,axiom,(
% 1.57/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.57/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.57/0.62  fof(f303,plain,(
% 1.57/0.62    spl7_1),
% 1.57/0.62    inference(avatar_contradiction_clause,[],[f301])).
% 1.57/0.62  fof(f301,plain,(
% 1.57/0.62    $false | spl7_1),
% 1.57/0.62    inference(resolution,[],[f278,f277])).
% 1.57/0.62  fof(f277,plain,(
% 1.57/0.62    ( ! [X2,X3] : (r2_hidden(sK4(k6_subset_1(X2,X3)),X2)) ) | spl7_1),
% 1.57/0.62    inference(resolution,[],[f270,f88])).
% 1.57/0.62  fof(f270,plain,(
% 1.57/0.62    ( ! [X0] : (r2_hidden(sK4(X0),X0)) ) | spl7_1),
% 1.57/0.62    inference(resolution,[],[f266,f64])).
% 1.57/0.62  fof(f64,plain,(
% 1.57/0.62    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f40])).
% 1.57/0.62  fof(f266,plain,(
% 1.57/0.62    ( ! [X1] : (~v1_xboole_0(X1)) ) | spl7_1),
% 1.57/0.62    inference(resolution,[],[f264,f63])).
% 1.57/0.62  fof(f264,plain,(
% 1.57/0.62    ( ! [X9] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X9,sK4(u1_struct_0(sK1)))),X9)) ) | spl7_1),
% 1.57/0.62    inference(resolution,[],[f224,f120])).
% 1.57/0.62  fof(f120,plain,(
% 1.57/0.62    m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | spl7_1),
% 1.57/0.62    inference(subsumption_resolution,[],[f118,f101])).
% 1.57/0.62  fof(f101,plain,(
% 1.57/0.62    ~v1_xboole_0(u1_struct_0(sK1)) | spl7_1),
% 1.57/0.62    inference(avatar_component_clause,[],[f100])).
% 1.57/0.62  fof(f118,plain,(
% 1.57/0.62    m1_subset_1(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | spl7_1),
% 1.57/0.62    inference(resolution,[],[f111,f67])).
% 1.57/0.62  fof(f67,plain,(
% 1.57/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.57/0.62    inference(cnf_transformation,[],[f41])).
% 1.57/0.62  fof(f111,plain,(
% 1.57/0.62    r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) | spl7_1),
% 1.57/0.62    inference(resolution,[],[f101,f64])).
% 1.57/0.62  fof(f278,plain,(
% 1.57/0.62    ( ! [X4,X5] : (~r2_hidden(sK4(k6_subset_1(X4,X5)),X5)) ) | spl7_1),
% 1.57/0.62    inference(resolution,[],[f270,f87])).
% 1.57/0.62  fof(f87,plain,(
% 1.57/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_subset_1(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.57/0.62    inference(equality_resolution,[],[f84])).
% 1.57/0.62  fof(f84,plain,(
% 1.57/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 1.57/0.62    inference(definition_unfolding,[],[f75,f65])).
% 1.57/0.63  fof(f75,plain,(
% 1.57/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.63    inference(cnf_transformation,[],[f48])).
% 1.57/0.63  % SZS output end Proof for theBenchmark
% 1.57/0.63  % (5443)------------------------------
% 1.57/0.63  % (5443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.63  % (5443)Termination reason: Refutation
% 1.57/0.63  
% 1.57/0.63  % (5443)Memory used [KB]: 10874
% 1.57/0.63  % (5443)Time elapsed: 0.185 s
% 1.57/0.63  % (5443)------------------------------
% 1.57/0.63  % (5443)------------------------------
% 1.57/0.63  % (5434)Success in time 0.261 s
%------------------------------------------------------------------------------
