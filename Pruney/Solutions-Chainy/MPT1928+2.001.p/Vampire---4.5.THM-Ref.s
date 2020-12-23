%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:37 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 444 expanded)
%              Number of leaves         :   19 ( 161 expanded)
%              Depth                    :   19
%              Number of atoms          :  564 (3436 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f106,f121,f128,f135])).

fof(f135,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | spl10_4
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f133,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( r1_xboole_0(sK2,sK3)
    & r1_waybel_0(sK0,sK1,sK3)
    & r1_waybel_0(sK0,sK1,sK2)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18,f17])).

% (32509)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(sK0,X1,X3)
              & r1_waybel_0(sK0,X1,X2) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( r1_xboole_0(X2,X3)
            & r1_waybel_0(sK0,X1,X3)
            & r1_waybel_0(sK0,X1,X2) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X3,X2] :
          ( r1_xboole_0(X2,X3)
          & r1_waybel_0(sK0,sK1,X3)
          & r1_waybel_0(sK0,sK1,X2) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3,X2] :
        ( r1_xboole_0(X2,X3)
        & r1_waybel_0(sK0,sK1,X3)
        & r1_waybel_0(sK0,sK1,X2) )
   => ( r1_xboole_0(sK2,sK3)
      & r1_waybel_0(sK0,sK1,sK3)
      & r1_waybel_0(sK0,sK1,sK2) ) ),
    introduced(choice_axiom,[])).

% (32523)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ~ ( r1_xboole_0(X2,X3)
                  & r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ~ ( r1_xboole_0(X2,X3)
                  & r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

% (32511)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).

fof(f133,plain,
    ( v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_2
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f132,f86])).

fof(f86,plain,
    ( l1_orders_2(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_1
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f132,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_2
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f131,f37])).

fof(f37,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f131,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_2
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f130,f90])).

fof(f90,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl10_2
  <=> m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f130,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ v7_waybel_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f129,f119])).

fof(f119,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl10_5
  <=> m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f129,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ v7_waybel_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | spl10_4 ),
    inference(resolution,[],[f116,f43])).

fof(f43,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ( ! [X3] :
                ( ~ r1_orders_2(X0,sK5(X0),X3)
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
                    & r1_orders_2(X0,X4,sK6(X0,X4,X5))
                    & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK4(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,sK4(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK5(X0),X3)
            | ~ r1_orders_2(X0,sK4(X0),X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
        & r1_orders_2(X0,X4,sK6(X0,X4,X5))
        & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ? [X6] :
                      ( r1_orders_2(X0,X5,X6)
                      & r1_orders_2(X0,X4,X6)
                      & m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_6)).

fof(f116,plain,
    ( ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl10_4
  <=> m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f128,plain,(
    spl10_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl10_5 ),
    inference(subsumption_resolution,[],[f126,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f126,plain,
    ( v2_struct_0(sK0)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f125,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f124,f36])).

fof(f124,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f123,f38])).

fof(f38,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f123,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_5 ),
    inference(subsumption_resolution,[],[f122,f39])).

fof(f39,plain,(
    r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f122,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_5 ),
    inference(resolution,[],[f120,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK7(X0,X1,X2,X3))
                      & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f30,f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK7(X0,X1,X2,X3))
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f120,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl10_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( ~ spl10_4
    | ~ spl10_5
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f112,f93,f89,f85,f118,f114])).

fof(f93,plain,
    ( spl10_3
  <=> ! [X0] :
        ( ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f112,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f111,f36])).

fof(f111,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f110,f86])).

fof(f110,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f109,f37])).

fof(f109,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ v7_waybel_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f108,f90])).

fof(f108,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ v7_waybel_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_3 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ v7_waybel_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_3 ),
    inference(resolution,[],[f94,f45])).

fof(f45,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1)) )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f106,plain,(
    spl10_2 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl10_2 ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,
    ( v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f103,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f101,f38])).

fof(f101,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f100,f40])).

fof(f40,plain,(
    r1_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK3)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | spl10_2 ),
    inference(resolution,[],[f91,f49])).

fof(f91,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f99,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,
    ( ~ l1_struct_0(sK0)
    | spl10_1 ),
    inference(resolution,[],[f96,f38])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK1,X0)
        | ~ l1_struct_0(X0) )
    | spl10_1 ),
    inference(resolution,[],[f87,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f87,plain,
    ( ~ l1_orders_2(sK1)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f95,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f80,f93,f89,f85])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
      | ~ l1_orders_2(sK1) ) ),
    inference(subsumption_resolution,[],[f79,f36])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f76,f37])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))
      | ~ v7_waybel_0(sK1)
      | ~ l1_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK6(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK1,sK8(sK0,sK1,sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),X0) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK3),X0)
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f73,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X0),sK2)
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f68,f39])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_waybel_0(sK0,sK1,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,X1),X0)
      | r2_hidden(k2_waybel_0(sK0,sK1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f67,f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r1_waybel_0(sK0,sK1,X1)
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,X1),X0)
      | v2_struct_0(sK1)
      | r2_hidden(k2_waybel_0(sK0,sK1,X0),X1) ) ),
    inference(resolution,[],[f66,f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_0(sK0,X0,X1)
      | ~ r1_orders_2(X0,sK8(sK0,X0,X1),X2)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(sK0,X0,X2),X1) ) ),
    inference(subsumption_resolution,[],[f65,f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK8(sK0,X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_0(sK0,X0,X1)
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(X0)
      | r2_hidden(k2_waybel_0(sK0,X0,X2),X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_orders_2(X1,sK8(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X1] :
      ( ~ r2_hidden(k2_waybel_0(sK0,sK1,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK3),X1) ) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f16,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f70,plain,(
    ! [X1] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,X1),sK3)
      | ~ r1_orders_2(sK1,sK8(sK0,sK1,sK3),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f68,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (804749313)
% 0.13/0.37  ipcrm: permission denied for id (806092802)
% 0.13/0.37  ipcrm: permission denied for id (804814851)
% 0.13/0.37  ipcrm: permission denied for id (806125572)
% 0.13/0.37  ipcrm: permission denied for id (806158341)
% 0.13/0.37  ipcrm: permission denied for id (804880390)
% 0.13/0.37  ipcrm: permission denied for id (804913159)
% 0.13/0.38  ipcrm: permission denied for id (806191112)
% 0.13/0.38  ipcrm: permission denied for id (809959433)
% 0.13/0.38  ipcrm: permission denied for id (806256650)
% 0.13/0.38  ipcrm: permission denied for id (806322188)
% 0.13/0.38  ipcrm: permission denied for id (804978701)
% 0.13/0.38  ipcrm: permission denied for id (810024974)
% 0.13/0.39  ipcrm: permission denied for id (805011471)
% 0.13/0.39  ipcrm: permission denied for id (810057744)
% 0.13/0.39  ipcrm: permission denied for id (810090513)
% 0.13/0.39  ipcrm: permission denied for id (806486034)
% 0.13/0.39  ipcrm: permission denied for id (806518803)
% 0.13/0.39  ipcrm: permission denied for id (806584341)
% 0.13/0.40  ipcrm: permission denied for id (806617110)
% 0.13/0.40  ipcrm: permission denied for id (806649879)
% 0.13/0.40  ipcrm: permission denied for id (806682648)
% 0.13/0.40  ipcrm: permission denied for id (810156057)
% 0.13/0.40  ipcrm: permission denied for id (806748186)
% 0.13/0.40  ipcrm: permission denied for id (806780955)
% 0.13/0.40  ipcrm: permission denied for id (806813724)
% 0.20/0.40  ipcrm: permission denied for id (806846493)
% 0.20/0.41  ipcrm: permission denied for id (811466782)
% 0.20/0.41  ipcrm: permission denied for id (810221599)
% 0.20/0.41  ipcrm: permission denied for id (806944800)
% 0.20/0.41  ipcrm: permission denied for id (805109793)
% 0.20/0.41  ipcrm: permission denied for id (806977570)
% 0.20/0.41  ipcrm: permission denied for id (807010339)
% 0.20/0.41  ipcrm: permission denied for id (807043108)
% 0.20/0.41  ipcrm: permission denied for id (807075877)
% 0.20/0.42  ipcrm: permission denied for id (807108646)
% 0.20/0.42  ipcrm: permission denied for id (807174183)
% 0.20/0.42  ipcrm: permission denied for id (807206952)
% 0.20/0.42  ipcrm: permission denied for id (810254377)
% 0.20/0.42  ipcrm: permission denied for id (810287146)
% 0.20/0.42  ipcrm: permission denied for id (807305259)
% 0.20/0.42  ipcrm: permission denied for id (807338028)
% 0.20/0.43  ipcrm: permission denied for id (805208109)
% 0.20/0.43  ipcrm: permission denied for id (807436334)
% 0.20/0.43  ipcrm: permission denied for id (807469103)
% 0.20/0.43  ipcrm: permission denied for id (807501872)
% 0.20/0.43  ipcrm: permission denied for id (810319921)
% 0.20/0.43  ipcrm: permission denied for id (811499570)
% 0.20/0.44  ipcrm: permission denied for id (807632947)
% 0.20/0.44  ipcrm: permission denied for id (807665716)
% 0.20/0.44  ipcrm: permission denied for id (805339190)
% 0.20/0.44  ipcrm: permission denied for id (807731255)
% 0.20/0.44  ipcrm: permission denied for id (807764024)
% 0.20/0.44  ipcrm: permission denied for id (807796793)
% 0.20/0.44  ipcrm: permission denied for id (807829562)
% 0.20/0.44  ipcrm: permission denied for id (807862331)
% 0.20/0.44  ipcrm: permission denied for id (805470268)
% 0.20/0.45  ipcrm: permission denied for id (805503037)
% 0.20/0.45  ipcrm: permission denied for id (807895102)
% 0.20/0.45  ipcrm: permission denied for id (805568575)
% 0.20/0.45  ipcrm: permission denied for id (807927872)
% 0.20/0.45  ipcrm: permission denied for id (805601345)
% 0.20/0.45  ipcrm: permission denied for id (807960642)
% 0.20/0.45  ipcrm: permission denied for id (807993411)
% 0.20/0.45  ipcrm: permission denied for id (808026180)
% 0.20/0.45  ipcrm: permission denied for id (810418245)
% 0.20/0.46  ipcrm: permission denied for id (808091718)
% 0.20/0.46  ipcrm: permission denied for id (808124487)
% 0.20/0.46  ipcrm: permission denied for id (810451016)
% 0.20/0.46  ipcrm: permission denied for id (810483785)
% 0.20/0.46  ipcrm: permission denied for id (808222794)
% 0.20/0.46  ipcrm: permission denied for id (808288332)
% 0.20/0.46  ipcrm: permission denied for id (808321101)
% 0.20/0.47  ipcrm: permission denied for id (808353870)
% 0.20/0.47  ipcrm: permission denied for id (811696207)
% 0.20/0.47  ipcrm: permission denied for id (810614865)
% 0.20/0.47  ipcrm: permission denied for id (810647634)
% 0.20/0.47  ipcrm: permission denied for id (808517715)
% 0.20/0.47  ipcrm: permission denied for id (805765204)
% 0.20/0.47  ipcrm: permission denied for id (811761749)
% 0.20/0.48  ipcrm: permission denied for id (810713174)
% 0.20/0.48  ipcrm: permission denied for id (808616023)
% 0.20/0.48  ipcrm: permission denied for id (805797976)
% 0.20/0.48  ipcrm: permission denied for id (810745945)
% 0.20/0.48  ipcrm: permission denied for id (808681562)
% 0.20/0.48  ipcrm: permission denied for id (808714331)
% 0.20/0.48  ipcrm: permission denied for id (810778716)
% 0.20/0.48  ipcrm: permission denied for id (810811485)
% 0.20/0.48  ipcrm: permission denied for id (808845406)
% 0.20/0.49  ipcrm: permission denied for id (810844255)
% 0.20/0.49  ipcrm: permission denied for id (808943713)
% 0.20/0.49  ipcrm: permission denied for id (811827298)
% 0.20/0.49  ipcrm: permission denied for id (809042019)
% 0.20/0.49  ipcrm: permission denied for id (809074788)
% 0.20/0.49  ipcrm: permission denied for id (809107557)
% 0.20/0.49  ipcrm: permission denied for id (810942566)
% 0.20/0.50  ipcrm: permission denied for id (811008104)
% 0.20/0.50  ipcrm: permission denied for id (809238633)
% 0.20/0.50  ipcrm: permission denied for id (809271402)
% 0.20/0.50  ipcrm: permission denied for id (811892843)
% 0.20/0.50  ipcrm: permission denied for id (809336940)
% 0.20/0.50  ipcrm: permission denied for id (811958381)
% 0.20/0.50  ipcrm: permission denied for id (809402478)
% 0.20/0.51  ipcrm: permission denied for id (811991151)
% 0.20/0.51  ipcrm: permission denied for id (809468016)
% 0.20/0.51  ipcrm: permission denied for id (812023921)
% 0.20/0.51  ipcrm: permission denied for id (805929074)
% 0.20/0.51  ipcrm: permission denied for id (812089460)
% 0.20/0.51  ipcrm: permission denied for id (809599093)
% 0.20/0.51  ipcrm: permission denied for id (809631862)
% 0.20/0.51  ipcrm: permission denied for id (811237495)
% 0.20/0.51  ipcrm: permission denied for id (812122232)
% 0.20/0.52  ipcrm: permission denied for id (809730169)
% 0.20/0.52  ipcrm: permission denied for id (811303034)
% 0.20/0.52  ipcrm: permission denied for id (812155003)
% 0.20/0.52  ipcrm: permission denied for id (805994620)
% 0.20/0.52  ipcrm: permission denied for id (809828477)
% 0.20/0.52  ipcrm: permission denied for id (806027390)
% 0.20/0.52  ipcrm: permission denied for id (809861247)
% 0.87/0.63  % (32507)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 1.06/0.63  % (32507)Refutation found. Thanks to Tanya!
% 1.06/0.63  % SZS status Theorem for theBenchmark
% 1.06/0.63  % SZS output start Proof for theBenchmark
% 1.06/0.63  fof(f136,plain,(
% 1.06/0.63    $false),
% 1.06/0.63    inference(avatar_sat_refutation,[],[f95,f99,f106,f121,f128,f135])).
% 1.06/0.63  fof(f135,plain,(
% 1.06/0.63    ~spl10_1 | ~spl10_2 | spl10_4 | ~spl10_5),
% 1.06/0.63    inference(avatar_contradiction_clause,[],[f134])).
% 1.06/0.63  fof(f134,plain,(
% 1.06/0.63    $false | (~spl10_1 | ~spl10_2 | spl10_4 | ~spl10_5)),
% 1.06/0.63    inference(subsumption_resolution,[],[f133,f36])).
% 1.06/0.63  fof(f36,plain,(
% 1.06/0.63    ~v2_struct_0(sK1)),
% 1.06/0.63    inference(cnf_transformation,[],[f20])).
% 1.06/0.63  fof(f20,plain,(
% 1.06/0.63    ((r1_xboole_0(sK2,sK3) & r1_waybel_0(sK0,sK1,sK3) & r1_waybel_0(sK0,sK1,sK2)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.06/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18,f17])).
% 1.06/0.63  % (32509)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 1.06/0.63  fof(f17,plain,(
% 1.06/0.63    ? [X0] : (? [X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X3,X2] : (r1_xboole_0(X2,X3) & r1_waybel_0(sK0,X1,X3) & r1_waybel_0(sK0,X1,X2)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.06/0.63    introduced(choice_axiom,[])).
% 1.06/0.63  fof(f18,plain,(
% 1.06/0.63    ? [X1] : (? [X3,X2] : (r1_xboole_0(X2,X3) & r1_waybel_0(sK0,X1,X3) & r1_waybel_0(sK0,X1,X2)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) => (? [X3,X2] : (r1_xboole_0(X2,X3) & r1_waybel_0(sK0,sK1,X3) & r1_waybel_0(sK0,sK1,X2)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & ~v2_struct_0(sK1))),
% 1.06/0.63    introduced(choice_axiom,[])).
% 1.06/0.63  fof(f19,plain,(
% 1.06/0.63    ? [X3,X2] : (r1_xboole_0(X2,X3) & r1_waybel_0(sK0,sK1,X3) & r1_waybel_0(sK0,sK1,X2)) => (r1_xboole_0(sK2,sK3) & r1_waybel_0(sK0,sK1,sK3) & r1_waybel_0(sK0,sK1,sK2))),
% 1.06/0.63    introduced(choice_axiom,[])).
% 1.06/0.64  % (32523)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 1.06/0.64  fof(f10,plain,(
% 1.06/0.64    ? [X0] : (? [X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.06/0.64    inference(flattening,[],[f9])).
% 1.06/0.64  fof(f9,plain,(
% 1.06/0.64    ? [X0] : (? [X1] : (? [X2,X3] : (r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.06/0.64    inference(ennf_transformation,[],[f8])).
% 1.06/0.64  fof(f8,plain,(
% 1.06/0.64    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 1.06/0.64    inference(pure_predicate_removal,[],[f6])).
% 1.06/0.64  fof(f6,negated_conjecture,(
% 1.06/0.64    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 1.06/0.64    inference(negated_conjecture,[],[f5])).
% 1.06/0.64  % (32511)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 1.06/0.64  fof(f5,conjecture,(
% 1.06/0.64    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 1.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_6)).
% 1.06/0.64  fof(f133,plain,(
% 1.06/0.64    v2_struct_0(sK1) | (~spl10_1 | ~spl10_2 | spl10_4 | ~spl10_5)),
% 1.06/0.64    inference(subsumption_resolution,[],[f132,f86])).
% 1.06/0.64  fof(f86,plain,(
% 1.06/0.64    l1_orders_2(sK1) | ~spl10_1),
% 1.06/0.64    inference(avatar_component_clause,[],[f85])).
% 1.06/0.64  fof(f85,plain,(
% 1.06/0.64    spl10_1 <=> l1_orders_2(sK1)),
% 1.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.06/0.64  fof(f132,plain,(
% 1.06/0.64    ~l1_orders_2(sK1) | v2_struct_0(sK1) | (~spl10_2 | spl10_4 | ~spl10_5)),
% 1.06/0.64    inference(subsumption_resolution,[],[f131,f37])).
% 1.06/0.64  fof(f37,plain,(
% 1.06/0.64    v7_waybel_0(sK1)),
% 1.06/0.64    inference(cnf_transformation,[],[f20])).
% 1.06/0.64  fof(f131,plain,(
% 1.06/0.64    ~v7_waybel_0(sK1) | ~l1_orders_2(sK1) | v2_struct_0(sK1) | (~spl10_2 | spl10_4 | ~spl10_5)),
% 1.06/0.64    inference(subsumption_resolution,[],[f130,f90])).
% 1.06/0.64  fof(f90,plain,(
% 1.06/0.64    m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~spl10_2),
% 1.06/0.64    inference(avatar_component_clause,[],[f89])).
% 1.06/0.64  fof(f89,plain,(
% 1.06/0.64    spl10_2 <=> m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1))),
% 1.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.06/0.64  fof(f130,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~v7_waybel_0(sK1) | ~l1_orders_2(sK1) | v2_struct_0(sK1) | (spl10_4 | ~spl10_5)),
% 1.06/0.64    inference(subsumption_resolution,[],[f129,f119])).
% 1.06/0.64  fof(f119,plain,(
% 1.06/0.64    m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~spl10_5),
% 1.06/0.64    inference(avatar_component_clause,[],[f118])).
% 1.06/0.64  fof(f118,plain,(
% 1.06/0.64    spl10_5 <=> m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1))),
% 1.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.06/0.64  fof(f129,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~v7_waybel_0(sK1) | ~l1_orders_2(sK1) | v2_struct_0(sK1) | spl10_4),
% 1.06/0.64    inference(resolution,[],[f116,f43])).
% 1.06/0.64  fof(f43,plain,(
% 1.06/0.64    ( ! [X4,X0,X5] : (m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.06/0.64    inference(cnf_transformation,[],[f26])).
% 1.06/0.64  fof(f26,plain,(
% 1.06/0.64    ! [X0] : (((v7_waybel_0(X0) | ((! [X3] : (~r1_orders_2(X0,sK5(X0),X3) | ~r1_orders_2(X0,sK4(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : ((r1_orders_2(X0,X5,sK6(X0,X4,X5)) & r1_orders_2(X0,X4,sK6(X0,X4,X5)) & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f22,f25,f24,f23])).
% 1.06/0.64  fof(f23,plain,(
% 1.06/0.64    ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK4(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 1.06/0.64    introduced(choice_axiom,[])).
% 1.06/0.64  fof(f24,plain,(
% 1.06/0.64    ! [X0] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,sK4(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (~r1_orders_2(X0,sK5(X0),X3) | ~r1_orders_2(X0,sK4(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.06/0.64    introduced(choice_axiom,[])).
% 1.06/0.64  fof(f25,plain,(
% 1.06/0.64    ! [X5,X4,X0] : (? [X6] : (r1_orders_2(X0,X5,X6) & r1_orders_2(X0,X4,X6) & m1_subset_1(X6,u1_struct_0(X0))) => (r1_orders_2(X0,X5,sK6(X0,X4,X5)) & r1_orders_2(X0,X4,sK6(X0,X4,X5)) & m1_subset_1(sK6(X0,X4,X5),u1_struct_0(X0))))),
% 1.06/0.64    introduced(choice_axiom,[])).
% 1.06/0.64  fof(f22,plain,(
% 1.06/0.64    ! [X0] : (((v7_waybel_0(X0) | ? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (? [X6] : (r1_orders_2(X0,X5,X6) & r1_orders_2(X0,X4,X6) & m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(rectify,[],[f21])).
% 1.06/0.64  fof(f21,plain,(
% 1.06/0.64    ! [X0] : (((v7_waybel_0(X0) | ? [X1] : (? [X2] : (! [X3] : (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(nnf_transformation,[],[f13])).
% 1.06/0.64  fof(f13,plain,(
% 1.06/0.64    ! [X0] : ((v7_waybel_0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(flattening,[],[f12])).
% 1.06/0.64  fof(f12,plain,(
% 1.06/0.64    ! [X0] : ((v7_waybel_0(X0) <=> ! [X1] : (! [X2] : (? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 1.06/0.64    inference(ennf_transformation,[],[f4])).
% 1.06/0.64  fof(f4,axiom,(
% 1.06/0.64    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ? [X3] : (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0)))))))),
% 1.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_6)).
% 1.06/0.64  fof(f116,plain,(
% 1.06/0.64    ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) | spl10_4),
% 1.06/0.64    inference(avatar_component_clause,[],[f114])).
% 1.06/0.64  fof(f114,plain,(
% 1.06/0.64    spl10_4 <=> m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 1.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.06/0.64  fof(f128,plain,(
% 1.06/0.64    spl10_5),
% 1.06/0.64    inference(avatar_contradiction_clause,[],[f127])).
% 1.06/0.64  fof(f127,plain,(
% 1.06/0.64    $false | spl10_5),
% 1.06/0.64    inference(subsumption_resolution,[],[f126,f34])).
% 1.06/0.64  fof(f34,plain,(
% 1.06/0.64    ~v2_struct_0(sK0)),
% 1.06/0.64    inference(cnf_transformation,[],[f20])).
% 1.06/0.64  fof(f126,plain,(
% 1.06/0.64    v2_struct_0(sK0) | spl10_5),
% 1.06/0.64    inference(subsumption_resolution,[],[f125,f35])).
% 1.06/0.64  fof(f35,plain,(
% 1.06/0.64    l1_struct_0(sK0)),
% 1.06/0.64    inference(cnf_transformation,[],[f20])).
% 1.06/0.64  fof(f125,plain,(
% 1.06/0.64    ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_5),
% 1.06/0.64    inference(subsumption_resolution,[],[f124,f36])).
% 1.06/0.64  fof(f124,plain,(
% 1.06/0.64    v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_5),
% 1.06/0.64    inference(subsumption_resolution,[],[f123,f38])).
% 1.06/0.64  fof(f38,plain,(
% 1.06/0.64    l1_waybel_0(sK1,sK0)),
% 1.06/0.64    inference(cnf_transformation,[],[f20])).
% 1.06/0.64  fof(f123,plain,(
% 1.06/0.64    ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_5),
% 1.06/0.64    inference(subsumption_resolution,[],[f122,f39])).
% 1.06/0.64  fof(f39,plain,(
% 1.06/0.64    r1_waybel_0(sK0,sK1,sK2)),
% 1.06/0.64    inference(cnf_transformation,[],[f20])).
% 1.06/0.64  fof(f122,plain,(
% 1.06/0.64    ~r1_waybel_0(sK0,sK1,sK2) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_5),
% 1.06/0.64    inference(resolution,[],[f120,f49])).
% 1.06/0.64  fof(f49,plain,(
% 1.06/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.06/0.64    inference(cnf_transformation,[],[f31])).
% 1.06/0.64  fof(f31,plain,(
% 1.06/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK7(X0,X1,X2,X3)) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK8(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f28,f30,f29])).
% 1.06/0.64  fof(f29,plain,(
% 1.06/0.64    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK7(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK7(X0,X1,X2,X3)) & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X1))))),
% 1.06/0.64    introduced(choice_axiom,[])).
% 1.06/0.64  fof(f30,plain,(
% 1.06/0.64    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK8(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 1.06/0.64    introduced(choice_axiom,[])).
% 1.06/0.64  fof(f28,plain,(
% 1.06/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(rectify,[],[f27])).
% 1.06/0.64  fof(f27,plain,(
% 1.06/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(nnf_transformation,[],[f15])).
% 1.06/0.64  fof(f15,plain,(
% 1.06/0.64    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.06/0.64    inference(flattening,[],[f14])).
% 1.06/0.64  fof(f14,plain,(
% 1.06/0.64    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.06/0.64    inference(ennf_transformation,[],[f2])).
% 1.06/0.64  fof(f2,axiom,(
% 1.06/0.64    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 1.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).
% 1.06/0.64  fof(f120,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | spl10_5),
% 1.06/0.64    inference(avatar_component_clause,[],[f118])).
% 1.06/0.64  fof(f121,plain,(
% 1.06/0.64    ~spl10_4 | ~spl10_5 | ~spl10_1 | ~spl10_2 | ~spl10_3),
% 1.06/0.64    inference(avatar_split_clause,[],[f112,f93,f89,f85,f118,f114])).
% 1.06/0.64  fof(f93,plain,(
% 1.06/0.64    spl10_3 <=> ! [X0] : (~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0)))),
% 1.06/0.64    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.06/0.64  fof(f112,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) | (~spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.06/0.64    inference(subsumption_resolution,[],[f111,f36])).
% 1.06/0.64  fof(f111,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) | v2_struct_0(sK1) | (~spl10_1 | ~spl10_2 | ~spl10_3)),
% 1.06/0.64    inference(subsumption_resolution,[],[f110,f86])).
% 1.06/0.64  fof(f110,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | v2_struct_0(sK1) | (~spl10_2 | ~spl10_3)),
% 1.06/0.64    inference(subsumption_resolution,[],[f109,f37])).
% 1.06/0.64  fof(f109,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~v7_waybel_0(sK1) | ~l1_orders_2(sK1) | v2_struct_0(sK1) | (~spl10_2 | ~spl10_3)),
% 1.06/0.64    inference(subsumption_resolution,[],[f108,f90])).
% 1.06/0.64  fof(f108,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~v7_waybel_0(sK1) | ~l1_orders_2(sK1) | v2_struct_0(sK1) | ~spl10_3),
% 1.06/0.64    inference(duplicate_literal_removal,[],[f107])).
% 1.06/0.64  fof(f107,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),sK8(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK0,sK1,sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~v7_waybel_0(sK1) | ~l1_orders_2(sK1) | v2_struct_0(sK1) | ~spl10_3),
% 1.06/0.64    inference(resolution,[],[f94,f45])).
% 1.06/0.64  fof(f45,plain,(
% 1.06/0.64    ( ! [X4,X0,X5] : (r1_orders_2(X0,X5,sK6(X0,X4,X5)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.06/0.64    inference(cnf_transformation,[],[f26])).
% 1.06/0.64  fof(f94,plain,(
% 1.06/0.64    ( ! [X0] : (~r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1))) ) | ~spl10_3),
% 1.06/0.64    inference(avatar_component_clause,[],[f93])).
% 1.06/0.64  fof(f106,plain,(
% 1.06/0.64    spl10_2),
% 1.06/0.64    inference(avatar_contradiction_clause,[],[f105])).
% 1.06/0.64  fof(f105,plain,(
% 1.06/0.64    $false | spl10_2),
% 1.06/0.64    inference(subsumption_resolution,[],[f104,f34])).
% 1.06/0.64  fof(f104,plain,(
% 1.06/0.64    v2_struct_0(sK0) | spl10_2),
% 1.06/0.64    inference(subsumption_resolution,[],[f103,f35])).
% 1.06/0.64  fof(f103,plain,(
% 1.06/0.64    ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_2),
% 1.06/0.64    inference(subsumption_resolution,[],[f102,f36])).
% 1.06/0.64  fof(f102,plain,(
% 1.06/0.64    v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_2),
% 1.06/0.64    inference(subsumption_resolution,[],[f101,f38])).
% 1.06/0.64  fof(f101,plain,(
% 1.06/0.64    ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_2),
% 1.06/0.64    inference(subsumption_resolution,[],[f100,f40])).
% 1.06/0.64  fof(f40,plain,(
% 1.06/0.64    r1_waybel_0(sK0,sK1,sK3)),
% 1.06/0.64    inference(cnf_transformation,[],[f20])).
% 1.06/0.64  fof(f100,plain,(
% 1.06/0.64    ~r1_waybel_0(sK0,sK1,sK3) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | spl10_2),
% 1.06/0.64    inference(resolution,[],[f91,f49])).
% 1.06/0.64  fof(f91,plain,(
% 1.06/0.64    ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | spl10_2),
% 1.06/0.64    inference(avatar_component_clause,[],[f89])).
% 1.06/0.64  fof(f99,plain,(
% 1.06/0.64    spl10_1),
% 1.06/0.64    inference(avatar_contradiction_clause,[],[f98])).
% 1.06/0.64  fof(f98,plain,(
% 1.06/0.64    $false | spl10_1),
% 1.06/0.64    inference(subsumption_resolution,[],[f97,f35])).
% 1.06/0.64  fof(f97,plain,(
% 1.06/0.64    ~l1_struct_0(sK0) | spl10_1),
% 1.06/0.64    inference(resolution,[],[f96,f38])).
% 1.06/0.64  fof(f96,plain,(
% 1.06/0.64    ( ! [X0] : (~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0)) ) | spl10_1),
% 1.06/0.64    inference(resolution,[],[f87,f42])).
% 1.06/0.64  fof(f42,plain,(
% 1.06/0.64    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.06/0.64    inference(cnf_transformation,[],[f11])).
% 1.06/0.64  fof(f11,plain,(
% 1.06/0.64    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.06/0.64    inference(ennf_transformation,[],[f3])).
% 1.06/0.64  fof(f3,axiom,(
% 1.06/0.64    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 1.06/0.64  fof(f87,plain,(
% 1.06/0.64    ~l1_orders_2(sK1) | spl10_1),
% 1.06/0.64    inference(avatar_component_clause,[],[f85])).
% 1.06/0.64  fof(f95,plain,(
% 1.06/0.64    ~spl10_1 | ~spl10_2 | spl10_3),
% 1.06/0.64    inference(avatar_split_clause,[],[f80,f93,f89,f85])).
% 1.06/0.64  fof(f80,plain,(
% 1.06/0.64    ( ! [X0] : (~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~l1_orders_2(sK1)) )),
% 1.06/0.64    inference(subsumption_resolution,[],[f79,f36])).
% 1.06/0.64  fof(f79,plain,(
% 1.06/0.64    ( ! [X0] : (~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~l1_orders_2(sK1) | v2_struct_0(sK1)) )),
% 1.06/0.64    inference(subsumption_resolution,[],[f76,f37])).
% 1.06/0.64  fof(f76,plain,(
% 1.06/0.64    ( ! [X0] : (~m1_subset_1(sK6(sK1,sK8(sK0,sK1,sK3),X0),u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK2),sK6(sK1,sK8(sK0,sK1,sK3),X0)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(sK8(sK0,sK1,sK3),u1_struct_0(sK1)) | ~v7_waybel_0(sK1) | ~l1_orders_2(sK1) | v2_struct_0(sK1)) )),
% 1.06/0.64    inference(resolution,[],[f75,f44])).
% 1.06/0.64  fof(f44,plain,(
% 1.06/0.64    ( ! [X4,X0,X5] : (r1_orders_2(X0,X4,sK6(X0,X4,X5)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.06/0.64    inference(cnf_transformation,[],[f26])).
% 1.06/0.64  fof(f75,plain,(
% 1.06/0.64    ( ! [X0] : (~r1_orders_2(sK1,sK8(sK0,sK1,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK2),X0)) )),
% 1.06/0.64    inference(duplicate_literal_removal,[],[f74])).
% 1.06/0.64  fof(f74,plain,(
% 1.06/0.64    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK3),X0) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.06/0.64    inference(resolution,[],[f73,f69])).
% 1.06/0.64  fof(f69,plain,(
% 1.06/0.64    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,X0),sK2) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK2),X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.06/0.64    inference(resolution,[],[f68,f39])).
% 1.06/0.64  fof(f68,plain,(
% 1.06/0.64    ( ! [X0,X1] : (~r1_waybel_0(sK0,sK1,X1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,X1),X0) | r2_hidden(k2_waybel_0(sK0,sK1,X0),X1)) )),
% 1.06/0.64    inference(subsumption_resolution,[],[f67,f36])).
% 1.06/0.64  fof(f67,plain,(
% 1.06/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~r1_waybel_0(sK0,sK1,X1) | ~r1_orders_2(sK1,sK8(sK0,sK1,X1),X0) | v2_struct_0(sK1) | r2_hidden(k2_waybel_0(sK0,sK1,X0),X1)) )),
% 1.06/0.64    inference(resolution,[],[f66,f38])).
% 1.06/0.64  fof(f66,plain,(
% 1.06/0.64    ( ! [X2,X0,X1] : (~l1_waybel_0(X0,sK0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_waybel_0(sK0,X0,X1) | ~r1_orders_2(X0,sK8(sK0,X0,X1),X2) | v2_struct_0(X0) | r2_hidden(k2_waybel_0(sK0,X0,X2),X1)) )),
% 1.06/0.64    inference(subsumption_resolution,[],[f65,f34])).
% 1.06/0.64  fof(f65,plain,(
% 1.06/0.64    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK8(sK0,X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_waybel_0(sK0,X0,X1) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r2_hidden(k2_waybel_0(sK0,X0,X2),X1) | v2_struct_0(sK0)) )),
% 1.06/0.64    inference(resolution,[],[f50,f35])).
% 1.06/0.64  fof(f50,plain,(
% 1.06/0.64    ( ! [X6,X2,X0,X1] : (~l1_struct_0(X0) | ~r1_orders_2(X1,sK8(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(X0,X1,X6),X2) | v2_struct_0(X0)) )),
% 1.06/0.64    inference(cnf_transformation,[],[f31])).
% 1.06/0.64  fof(f73,plain,(
% 1.06/0.64    ( ! [X1] : (~r2_hidden(k2_waybel_0(sK0,sK1,X1),sK2) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK3),X1)) )),
% 1.06/0.64    inference(resolution,[],[f70,f57])).
% 1.06/0.64  fof(f57,plain,(
% 1.06/0.64    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK2)) )),
% 1.06/0.64    inference(resolution,[],[f56,f41])).
% 1.06/0.64  fof(f41,plain,(
% 1.06/0.64    r1_xboole_0(sK2,sK3)),
% 1.06/0.64    inference(cnf_transformation,[],[f20])).
% 1.06/0.64  fof(f56,plain,(
% 1.06/0.64    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.06/0.64    inference(cnf_transformation,[],[f33])).
% 1.06/0.64  fof(f33,plain,(
% 1.06/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.06/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f16,f32])).
% 1.06/0.64  fof(f32,plain,(
% 1.06/0.64    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.06/0.64    introduced(choice_axiom,[])).
% 1.06/0.64  fof(f16,plain,(
% 1.06/0.64    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.06/0.64    inference(ennf_transformation,[],[f7])).
% 1.06/0.64  fof(f7,plain,(
% 1.06/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.06/0.64    inference(rectify,[],[f1])).
% 1.06/0.64  fof(f1,axiom,(
% 1.06/0.64    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.06/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.06/0.64  fof(f70,plain,(
% 1.06/0.64    ( ! [X1] : (r2_hidden(k2_waybel_0(sK0,sK1,X1),sK3) | ~r1_orders_2(sK1,sK8(sK0,sK1,sK3),X1) | ~m1_subset_1(X1,u1_struct_0(sK1))) )),
% 1.06/0.64    inference(resolution,[],[f68,f40])).
% 1.06/0.64  % SZS output end Proof for theBenchmark
% 1.06/0.64  % (32507)------------------------------
% 1.06/0.64  % (32507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.06/0.64  % (32507)Termination reason: Refutation
% 1.06/0.64  
% 1.06/0.64  % (32507)Memory used [KB]: 5373
% 1.06/0.64  % (32507)Time elapsed: 0.053 s
% 1.06/0.64  % (32507)------------------------------
% 1.06/0.64  % (32507)------------------------------
% 1.06/0.64  % (32513)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 1.06/0.64  % (32341)Success in time 0.284 s
%------------------------------------------------------------------------------
