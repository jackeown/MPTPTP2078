%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1571+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 314 expanded)
%              Number of leaves         :   17 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  563 (1244 expanded)
%              Number of equality atoms :   36 (  95 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f54,f92,f110,f126,f141,f171,f178,f204,f213,f223,f259])).

fof(f259,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f257,f43])).

fof(f43,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_3
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f257,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | spl5_5
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f256,f162])).

fof(f162,plain,
    ( r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_13
  <=> r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f256,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | spl5_5
    | ~ spl5_14 ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | spl5_5
    | ~ spl5_14 ),
    inference(resolution,[],[f202,f237])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK4(sK0,X0,sK2))
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,sK1,sK4(sK0,X0,sK2)) )
    | spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(resolution,[],[f224,f14])).

fof(f14,plain,(
    ! [X3] :
      ( r1_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r1_lattice3(sK0,sK1,X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <=> r1_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                  <=> r1_lattice3(X0,X2,X3) ) )
              & r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,sK4(sK0,X0,sK2))
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK4(sK0,X0,sK2)) )
    | spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(resolution,[],[f87,f60])).

fof(f60,plain,
    ( ! [X2,X3] :
        ( r2_yellow_0(sK0,X2)
        | ~ r1_lattice3(sK0,X3,sK4(sK0,X3,X2))
        | ~ r2_yellow_0(sK0,X3)
        | ~ r1_lattice3(sK0,X2,sK4(sK0,X3,X2)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f46,f38])).

fof(f38,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f46,plain,
    ( ! [X2,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_lattice3(sK0,X2,sK4(sK0,X3,X2))
        | ~ r1_lattice3(sK0,X3,sK4(sK0,X3,X2))
        | ~ r2_yellow_0(sK0,X3)
        | r2_yellow_0(sK0,X2) )
    | spl5_1 ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f33,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f87,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_5
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f202,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl5_14
  <=> m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f223,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_9
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f121,f124])).

fof(f124,plain,
    ( r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_10
  <=> r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f121,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_9 ),
    inference(subsumption_resolution,[],[f120,f53])).

fof(f53,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_4
  <=> k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f120,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_9 ),
    inference(subsumption_resolution,[],[f119,f38])).

fof(f119,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_9 ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f118,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | spl5_9 ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f47,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f117,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | spl5_9 ),
    inference(resolution,[],[f109,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

% (23017)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (23030)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (23030)Refutation not found, incomplete strategy% (23030)------------------------------
% (23030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23030)Termination reason: Refutation not found, incomplete strategy

% (23030)Memory used [KB]: 1663
% (23030)Time elapsed: 0.073 s
% (23030)------------------------------
% (23030)------------------------------
% (23016)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f109,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k2_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_9
  <=> m1_subset_1(sK3(sK0,sK1,k2_yellow_0(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f213,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_14 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_14 ),
    inference(subsumption_resolution,[],[f211,f87])).

fof(f211,plain,
    ( r2_yellow_0(sK0,sK2)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_14 ),
    inference(subsumption_resolution,[],[f210,f43])).

fof(f210,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | spl5_1
    | ~ spl5_2
    | spl5_14 ),
    inference(subsumption_resolution,[],[f209,f33])).

fof(f209,plain,
    ( v2_struct_0(sK0)
    | ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | spl5_14 ),
    inference(subsumption_resolution,[],[f208,f38])).

fof(f208,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,sK2)
    | spl5_14 ),
    inference(resolution,[],[f203,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f203,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f204,plain,
    ( ~ spl5_14
    | ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f194,f161,f157,f201])).

fof(f157,plain,
    ( spl5_12
  <=> r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f194,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl5_12
    | spl5_13 ),
    inference(subsumption_resolution,[],[f166,f159])).

fof(f159,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f166,plain,
    ( ~ r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_13 ),
    inference(resolution,[],[f163,f13])).

fof(f13,plain,(
    ! [X3] :
      ( r1_lattice3(sK0,sK1,X3)
      | ~ r1_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f163,plain,
    ( ~ r1_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f178,plain,
    ( ~ spl5_2
    | ~ spl5_5
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5
    | spl5_11 ),
    inference(subsumption_resolution,[],[f148,f86])).

fof(f86,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f148,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | spl5_11 ),
    inference(resolution,[],[f140,f58])).

fof(f58,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2))
        | ~ r2_yellow_0(sK0,X2) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f56,f38])).

fof(f56,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f140,plain,
    ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_11
  <=> r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f171,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_12
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_12
    | spl5_13 ),
    inference(subsumption_resolution,[],[f169,f158])).

fof(f158,plain,
    ( ~ r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f169,plain,
    ( r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_13 ),
    inference(subsumption_resolution,[],[f167,f43])).

fof(f167,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r1_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | spl5_5
    | spl5_13 ),
    inference(resolution,[],[f163,f100])).

fof(f100,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,X1,sK4(sK0,X1,sK2))
        | ~ r2_yellow_0(sK0,X1)
        | r1_lattice3(sK0,sK2,sK4(sK0,X1,sK2)) )
    | spl5_1
    | ~ spl5_2
    | spl5_5 ),
    inference(resolution,[],[f87,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X1,sK4(sK0,X1,X0))
        | ~ r2_yellow_0(sK0,X1)
        | r1_lattice3(sK0,X0,sK4(sK0,X1,X0)) )
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f45,f38])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,sK4(sK0,X1,X0))
        | r1_lattice3(sK0,X1,sK4(sK0,X1,X0))
        | ~ r2_yellow_0(sK0,X1)
        | r2_yellow_0(sK0,X0) )
    | spl5_1 ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f141,plain,
    ( ~ spl5_11
    | ~ spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f136,f123,f36,f138])).

fof(f136,plain,
    ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ spl5_2
    | spl5_10 ),
    inference(subsumption_resolution,[],[f135,f47])).

fof(f135,plain,
    ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | spl5_10 ),
    inference(resolution,[],[f125,f13])).

fof(f125,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( ~ spl5_10
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_8 ),
    inference(avatar_split_clause,[],[f116,f103,f51,f41,f36,f123])).

fof(f103,plain,
    ( spl5_8
  <=> r1_lattice3(sK0,sK1,sK3(sK0,sK1,k2_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f116,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | spl5_8 ),
    inference(subsumption_resolution,[],[f115,f53])).

fof(f115,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_8 ),
    inference(subsumption_resolution,[],[f114,f47])).

fof(f114,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_8 ),
    inference(subsumption_resolution,[],[f113,f43])).

fof(f113,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | spl5_8 ),
    inference(resolution,[],[f105,f48])).

fof(f48,plain,
    ( ! [X2,X1] :
        ( r1_lattice3(sK0,X2,sK3(sK0,X2,X1))
        | ~ r2_yellow_0(sK0,X2)
        | ~ r1_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_yellow_0(sK0,X2) = X1 )
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3(sK0,sK1,k2_yellow_0(sK0,sK2)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f110,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | spl5_6 ),
    inference(avatar_split_clause,[],[f101,f89,f107,f103])).

fof(f89,plain,
    ( spl5_6
  <=> r1_lattice3(sK0,sK2,sK3(sK0,sK1,k2_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f101,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,k2_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK3(sK0,sK1,k2_yellow_0(sK0,sK2)))
    | spl5_6 ),
    inference(resolution,[],[f91,f14])).

fof(f91,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3(sK0,sK1,k2_yellow_0(sK0,sK2)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f92,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f80,f51,f41,f36,f89,f85])).

fof(f80,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3(sK0,sK1,k2_yellow_0(sK0,sK2)))
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f79,f53])).

fof(f79,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3(sK0,sK1,k2_yellow_0(sK0,sK2)))
    | ~ r2_yellow_0(sK0,sK2)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3(sK0,sK1,k2_yellow_0(sK0,sK2)))
    | ~ r2_yellow_0(sK0,sK2)
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,sK2)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f73,f58])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,X0))
        | ~ r1_lattice3(sK0,X0,sK3(sK0,sK1,k2_yellow_0(sK0,X0)))
        | ~ r2_yellow_0(sK0,X0)
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f70,f47])).

fof(f70,plain,
    ( ! [X0] :
        ( k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK3(sK0,sK1,k2_yellow_0(sK0,X0)))
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,X0))
        | ~ m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f67,f13])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,sK3(sK0,sK1,k2_yellow_0(sK0,X0)))
        | ~ r2_yellow_0(sK0,X0) )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(resolution,[],[f66,f43])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1)
        | ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
        | ~ r1_lattice3(sK0,X1,sK3(sK0,X0,k2_yellow_0(sK0,X1)))
        | ~ r2_yellow_0(sK0,X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f65,f38])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1)
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X1,sK3(sK0,X0,k2_yellow_0(sK0,X1)))
        | ~ r2_yellow_0(sK0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f64,f47])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1)
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X1,sK3(sK0,X0,k2_yellow_0(sK0,X1)))
        | ~ r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(k2_yellow_0(sK0,X1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1)
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X1,sK3(sK0,X0,k2_yellow_0(sK0,X1)))
        | ~ r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(k2_yellow_0(sK0,X1),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
        | ~ l1_orders_2(sK0)
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f62,f19])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,X0,k2_yellow_0(sK0,X1)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1)
        | ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X1,sK3(sK0,X0,k2_yellow_0(sK0,X1)))
        | ~ r2_yellow_0(sK0,X1) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f61,f47])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,X1))
        | ~ m1_subset_1(k2_yellow_0(sK0,X1),u1_struct_0(sK0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1)
        | ~ m1_subset_1(sK3(sK0,X0,k2_yellow_0(sK0,X1)),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,sK3(sK0,X0,k2_yellow_0(sK0,X1)))
        | ~ r2_yellow_0(sK0,X1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ r2_yellow_0(sK0,X0) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f55,f38])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,
    ( ! [X4,X3] :
        ( ~ r1_orders_2(sK0,sK3(sK0,X4,X3),X3)
        | ~ r2_yellow_0(sK0,X4)
        | ~ r1_lattice3(sK0,X4,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_yellow_0(sK0,X4) = X3 )
    | ~ spl5_2 ),
    inference(resolution,[],[f38,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f16,f51])).

fof(f16,plain,(
    k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f15,f41])).

fof(f15,plain,(
    r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
