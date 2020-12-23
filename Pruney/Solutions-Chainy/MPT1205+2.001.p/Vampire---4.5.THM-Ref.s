%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:39 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 244 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :  623 ( 961 expanded)
%              Number of equality atoms :   54 (  80 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f89,f94,f105,f121,f125,f136,f141,f150,f155,f165,f173,f178,f227])).

fof(f227,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | spl3_16
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f222,f164])).

fof(f164,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_16
  <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f222,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(resolution,[],[f206,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),X0) = X0 )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f205,f112])).

fof(f112,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_10
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),X0) = X0
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k5_lattices(sK0),X0) = X0
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(resolution,[],[f191,f106])).

% (9868)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (9865)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (9867)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (9863)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (9857)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (9851)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (9851)Refutation not found, incomplete strategy% (9851)------------------------------
% (9851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9851)Termination reason: Refutation not found, incomplete strategy

% (9851)Memory used [KB]: 10618
% (9851)Time elapsed: 0.088 s
% (9851)------------------------------
% (9851)------------------------------
% (9852)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f106,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattices(sK0,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k1_lattices(sK0,X6,X7) = X7
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f77,f100])).

fof(f100,plain,
    ( l2_lattices(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_8
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f77,plain,
    ( ! [X6,X7] :
        ( ~ l2_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k1_lattices(sK0,X6,X7) = X7
        | ~ r1_lattices(sK0,X6,X7) )
    | spl3_1 ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f57,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f191,plain,
    ( ! [X1] :
        ( r1_lattices(sK0,k5_lattices(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f186,f112])).

fof(f186,plain,
    ( ! [X1] :
        ( r1_lattices(sK0,k5_lattices(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X1] :
        ( r1_lattices(sK0,k5_lattices(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(superposition,[],[f181,f127])).

fof(f127,plain,
    ( ! [X2] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f126,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0)) )
    | spl3_1
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f84,f116])).

fof(f116,plain,
    ( l1_lattices(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_11
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f84,plain,
    ( ! [X2] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0)) )
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f81,f57])).

fof(f81,plain,
    ( ! [X2] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f67,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X2,X1) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f67,plain,
    ( v13_lattices(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k2_lattices(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(superposition,[],[f168,f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f168,plain,
    ( ! [X8,X9] :
        ( r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_17
  <=> ! [X9,X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8)
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f178,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_18 ),
    inference(subsumption_resolution,[],[f176,f72])).

fof(f72,plain,
    ( l3_lattices(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f176,plain,
    ( ~ l3_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | spl3_18 ),
    inference(subsumption_resolution,[],[f175,f62])).

fof(f62,plain,
    ( v10_lattices(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f175,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_1
    | spl3_18 ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f174,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_18 ),
    inference(resolution,[],[f172,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f172,plain,
    ( ~ v8_lattices(sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_18
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f173,plain,
    ( spl3_17
    | ~ spl3_18
    | spl3_1
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f160,f133,f70,f55,f170,f167])).

fof(f133,plain,
    ( spl3_13
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f160,plain,
    ( ! [X8,X9] :
        ( ~ v8_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8) )
    | spl3_1
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f159,f72])).

fof(f159,plain,
    ( ! [X8,X9] :
        ( ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8) )
    | spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f78,f134])).

fof(f134,plain,
    ( v6_lattices(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f78,plain,
    ( ! [X8,X9] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8) )
    | spl3_1 ),
    inference(resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(f165,plain,
    ( ~ spl3_16
    | ~ spl3_5
    | spl3_6
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f158,f144,f111,f91,f86,f162])).

fof(f91,plain,
    ( spl3_6
  <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f144,plain,
    ( spl3_14
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f158,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl3_5
    | spl3_6
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f157,f88])).

fof(f157,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_6
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f156,f112])).

fof(f156,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f93,f145])).

fof(f145,plain,
    ( ! [X2,X3] :
        ( k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f93,plain,
    ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f155,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_15 ),
    inference(subsumption_resolution,[],[f153,f72])).

fof(f153,plain,
    ( ~ l3_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | spl3_15 ),
    inference(subsumption_resolution,[],[f152,f62])).

fof(f152,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_1
    | spl3_15 ),
    inference(subsumption_resolution,[],[f151,f57])).

fof(f151,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_15 ),
    inference(resolution,[],[f149,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f149,plain,
    ( ~ v4_lattices(sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_15
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f150,plain,
    ( spl3_14
    | ~ spl3_15
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f142,f99,f55,f147,f144])).

fof(f142,plain,
    ( ! [X2,X3] :
        ( ~ v4_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3) )
    | spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f75,f100])).

fof(f75,plain,
    ( ! [X2,X3] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3) )
    | spl3_1 ),
    inference(resolution,[],[f57,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f141,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_13 ),
    inference(subsumption_resolution,[],[f139,f72])).

fof(f139,plain,
    ( ~ l3_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | spl3_13 ),
    inference(subsumption_resolution,[],[f138,f62])).

fof(f138,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_1
    | spl3_13 ),
    inference(subsumption_resolution,[],[f137,f57])).

fof(f137,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl3_13 ),
    inference(resolution,[],[f135,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f135,plain,
    ( ~ v6_lattices(sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f136,plain,
    ( spl3_12
    | ~ spl3_13
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f128,f115,f55,f133,f130])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ v6_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) )
    | spl3_1
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f74,f116])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) )
    | spl3_1 ),
    inference(resolution,[],[f57,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f125,plain,
    ( spl3_1
    | spl3_10
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl3_1
    | spl3_10
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f123,f57])).

fof(f123,plain,
    ( v2_struct_0(sK0)
    | spl3_10
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f122,f116])).

fof(f122,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl3_10 ),
    inference(resolution,[],[f113,f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f113,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f121,plain,
    ( ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f119,f72])).

fof(f119,plain,
    ( ~ l3_lattices(sK0)
    | spl3_11 ),
    inference(resolution,[],[f117,f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f117,plain,
    ( ~ l1_lattices(sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f105,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl3_4
    | spl3_8 ),
    inference(subsumption_resolution,[],[f103,f72])).

fof(f103,plain,
    ( ~ l3_lattices(sK0)
    | spl3_8 ),
    inference(resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f101,plain,
    ( ~ l2_lattices(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f94,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f29,f91])).

fof(f29,plain,(
    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

fof(f89,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f86])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f70])).

fof(f33,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:08:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.45  % (9850)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.46  % (9861)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.18/0.46  % (9856)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.47  % (9854)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.47  % (9858)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.18/0.47  % (9864)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.47  % (9853)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.47  % (9855)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.47  % (9870)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.47  % (9869)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.47  % (9870)Refutation not found, incomplete strategy% (9870)------------------------------
% 0.18/0.47  % (9870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (9870)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (9870)Memory used [KB]: 10618
% 0.18/0.47  % (9870)Time elapsed: 0.079 s
% 0.18/0.47  % (9870)------------------------------
% 0.18/0.47  % (9870)------------------------------
% 0.18/0.47  % (9866)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.18/0.47  % (9853)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f231,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f89,f94,f105,f121,f125,f136,f141,f150,f155,f165,f173,f178,f227])).
% 0.18/0.47  fof(f227,plain,(
% 0.18/0.47    spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | spl3_16 | ~spl3_17),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f226])).
% 0.18/0.47  fof(f226,plain,(
% 0.18/0.47    $false | (spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | spl3_16 | ~spl3_17)),
% 0.18/0.47    inference(subsumption_resolution,[],[f222,f164])).
% 0.18/0.47  fof(f164,plain,(
% 0.18/0.47    sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1) | spl3_16),
% 0.18/0.47    inference(avatar_component_clause,[],[f162])).
% 0.18/0.47  fof(f162,plain,(
% 0.18/0.47    spl3_16 <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.18/0.47  fof(f222,plain,(
% 0.18/0.47    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | (spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.18/0.47    inference(resolution,[],[f206,f88])).
% 0.18/0.47  fof(f88,plain,(
% 0.18/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f86])).
% 0.18/0.47  fof(f86,plain,(
% 0.18/0.47    spl3_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.18/0.47  fof(f206,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X0) = X0) ) | (spl3_1 | ~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.18/0.47    inference(subsumption_resolution,[],[f205,f112])).
% 0.18/0.47  fof(f112,plain,(
% 0.18/0.47    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl3_10),
% 0.18/0.47    inference(avatar_component_clause,[],[f111])).
% 0.18/0.47  fof(f111,plain,(
% 0.18/0.47    spl3_10 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.18/0.47  fof(f205,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X0) = X0 | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.18/0.47    inference(duplicate_literal_removal,[],[f204])).
% 0.18/0.47  fof(f204,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k5_lattices(sK0),X0) = X0 | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.18/0.47    inference(resolution,[],[f191,f106])).
% 0.18/0.48  % (9868)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.18/0.48  % (9865)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.48  % (9867)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.18/0.48  % (9863)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.48  % (9857)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.48  % (9851)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.49  % (9851)Refutation not found, incomplete strategy% (9851)------------------------------
% 0.18/0.49  % (9851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (9851)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (9851)Memory used [KB]: 10618
% 0.18/0.49  % (9851)Time elapsed: 0.088 s
% 0.18/0.49  % (9851)------------------------------
% 0.18/0.49  % (9851)------------------------------
% 0.18/0.49  % (9852)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.49  fof(f106,plain,(
% 0.18/0.49    ( ! [X6,X7] : (~r1_lattices(sK0,X6,X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | k1_lattices(sK0,X6,X7) = X7 | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_8)),
% 0.18/0.49    inference(subsumption_resolution,[],[f77,f100])).
% 0.18/0.49  fof(f100,plain,(
% 0.18/0.49    l2_lattices(sK0) | ~spl3_8),
% 0.18/0.49    inference(avatar_component_clause,[],[f99])).
% 0.18/0.49  fof(f99,plain,(
% 0.18/0.49    spl3_8 <=> l2_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.18/0.49  fof(f77,plain,(
% 0.18/0.49    ( ! [X6,X7] : (~l2_lattices(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X7,u1_struct_0(sK0)) | k1_lattices(sK0,X6,X7) = X7 | ~r1_lattices(sK0,X6,X7)) ) | spl3_1),
% 0.18/0.49    inference(resolution,[],[f57,f44])).
% 0.18/0.49  fof(f44,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f19])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.18/0.49    inference(flattening,[],[f18])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.18/0.49  fof(f57,plain,(
% 0.18/0.49    ~v2_struct_0(sK0) | spl3_1),
% 0.18/0.49    inference(avatar_component_clause,[],[f55])).
% 0.18/0.49  fof(f55,plain,(
% 0.18/0.49    spl3_1 <=> v2_struct_0(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.18/0.49  fof(f191,plain,(
% 0.18/0.49    ( ! [X1] : (r1_lattices(sK0,k5_lattices(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.18/0.49    inference(subsumption_resolution,[],[f186,f112])).
% 0.18/0.49  fof(f186,plain,(
% 0.18/0.49    ( ! [X1] : (r1_lattices(sK0,k5_lattices(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.18/0.49    inference(duplicate_literal_removal,[],[f185])).
% 0.18/0.49  fof(f185,plain,(
% 0.18/0.49    ( ! [X1] : (r1_lattices(sK0,k5_lattices(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.18/0.49    inference(superposition,[],[f181,f127])).
% 0.18/0.49  fof(f127,plain,(
% 0.18/0.49    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_3 | ~spl3_10 | ~spl3_11)),
% 0.18/0.49    inference(subsumption_resolution,[],[f126,f112])).
% 0.18/0.49  fof(f126,plain,(
% 0.18/0.49    ( ! [X2] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0))) ) | (spl3_1 | ~spl3_3 | ~spl3_11)),
% 0.18/0.49    inference(subsumption_resolution,[],[f84,f116])).
% 0.18/0.49  fof(f116,plain,(
% 0.18/0.49    l1_lattices(sK0) | ~spl3_11),
% 0.18/0.49    inference(avatar_component_clause,[],[f115])).
% 0.18/0.49  fof(f115,plain,(
% 0.18/0.49    spl3_11 <=> l1_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.18/0.49  fof(f84,plain,(
% 0.18/0.49    ( ! [X2] : (~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0))) ) | (spl3_1 | ~spl3_3)),
% 0.18/0.49    inference(subsumption_resolution,[],[f81,f57])).
% 0.18/0.49  fof(f81,plain,(
% 0.18/0.49    ( ! [X2] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X2,k5_lattices(sK0))) ) | ~spl3_3),
% 0.18/0.49    inference(resolution,[],[f67,f52])).
% 0.18/0.49  fof(f52,plain,(
% 0.18/0.49    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 0.18/0.49    inference(equality_resolution,[],[f48])).
% 0.18/0.49  fof(f48,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X2,X1) = X1 | k5_lattices(X0) != X1) )),
% 0.18/0.49    inference(cnf_transformation,[],[f23])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.18/0.49    inference(flattening,[],[f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 0.18/0.49  fof(f67,plain,(
% 0.18/0.49    v13_lattices(sK0) | ~spl3_3),
% 0.18/0.49    inference(avatar_component_clause,[],[f65])).
% 0.18/0.49  fof(f65,plain,(
% 0.18/0.49    spl3_3 <=> v13_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.18/0.49  fof(f181,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl3_12 | ~spl3_17)),
% 0.18/0.49    inference(duplicate_literal_removal,[],[f180])).
% 0.18/0.49  fof(f180,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,X0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl3_12 | ~spl3_17)),
% 0.18/0.49    inference(superposition,[],[f168,f131])).
% 0.18/0.49  fof(f131,plain,(
% 0.18/0.49    ( ! [X0,X1] : (k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl3_12),
% 0.18/0.49    inference(avatar_component_clause,[],[f130])).
% 0.18/0.49  fof(f130,plain,(
% 0.18/0.49    spl3_12 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.18/0.49  fof(f168,plain,(
% 0.18/0.49    ( ! [X8,X9] : (r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0))) ) | ~spl3_17),
% 0.18/0.49    inference(avatar_component_clause,[],[f167])).
% 0.18/0.49  fof(f167,plain,(
% 0.18/0.49    spl3_17 <=> ! [X9,X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8) | ~m1_subset_1(X9,u1_struct_0(sK0)))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.18/0.49  fof(f178,plain,(
% 0.18/0.49    spl3_1 | ~spl3_2 | ~spl3_4 | spl3_18),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f177])).
% 0.18/0.49  fof(f177,plain,(
% 0.18/0.49    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | spl3_18)),
% 0.18/0.49    inference(subsumption_resolution,[],[f176,f72])).
% 0.18/0.49  fof(f72,plain,(
% 0.18/0.49    l3_lattices(sK0) | ~spl3_4),
% 0.18/0.49    inference(avatar_component_clause,[],[f70])).
% 0.18/0.49  fof(f70,plain,(
% 0.18/0.49    spl3_4 <=> l3_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.18/0.49  fof(f176,plain,(
% 0.18/0.49    ~l3_lattices(sK0) | (spl3_1 | ~spl3_2 | spl3_18)),
% 0.18/0.49    inference(subsumption_resolution,[],[f175,f62])).
% 0.18/0.49  fof(f62,plain,(
% 0.18/0.49    v10_lattices(sK0) | ~spl3_2),
% 0.18/0.49    inference(avatar_component_clause,[],[f60])).
% 0.18/0.49  fof(f60,plain,(
% 0.18/0.49    spl3_2 <=> v10_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.18/0.49  fof(f175,plain,(
% 0.18/0.49    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl3_1 | spl3_18)),
% 0.18/0.49    inference(subsumption_resolution,[],[f174,f57])).
% 0.18/0.49  fof(f174,plain,(
% 0.18/0.49    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl3_18),
% 0.18/0.49    inference(resolution,[],[f172,f40])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f15])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.18/0.49    inference(flattening,[],[f14])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.18/0.49  fof(f172,plain,(
% 0.18/0.49    ~v8_lattices(sK0) | spl3_18),
% 0.18/0.49    inference(avatar_component_clause,[],[f170])).
% 0.18/0.49  fof(f170,plain,(
% 0.18/0.49    spl3_18 <=> v8_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.18/0.49  fof(f173,plain,(
% 0.18/0.49    spl3_17 | ~spl3_18 | spl3_1 | ~spl3_4 | ~spl3_13),
% 0.18/0.49    inference(avatar_split_clause,[],[f160,f133,f70,f55,f170,f167])).
% 0.18/0.49  fof(f133,plain,(
% 0.18/0.49    spl3_13 <=> v6_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.18/0.49  fof(f160,plain,(
% 0.18/0.49    ( ! [X8,X9] : (~v8_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8)) ) | (spl3_1 | ~spl3_4 | ~spl3_13)),
% 0.18/0.49    inference(subsumption_resolution,[],[f159,f72])).
% 0.18/0.49  fof(f159,plain,(
% 0.18/0.49    ( ! [X8,X9] : (~v8_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8)) ) | (spl3_1 | ~spl3_13)),
% 0.18/0.49    inference(subsumption_resolution,[],[f78,f134])).
% 0.18/0.49  fof(f134,plain,(
% 0.18/0.49    v6_lattices(sK0) | ~spl3_13),
% 0.18/0.49    inference(avatar_component_clause,[],[f133])).
% 0.18/0.49  fof(f78,plain,(
% 0.18/0.49    ( ! [X8,X9] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X8,X9),X8)) ) | spl3_1),
% 0.18/0.49    inference(resolution,[],[f57,f42])).
% 0.18/0.49  fof(f42,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,k4_lattices(X0,X1,X2),X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.18/0.49    inference(flattening,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f8])).
% 0.18/0.49  fof(f8,axiom,(
% 0.18/0.49    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).
% 0.18/0.49  fof(f165,plain,(
% 0.18/0.49    ~spl3_16 | ~spl3_5 | spl3_6 | ~spl3_10 | ~spl3_14),
% 0.18/0.49    inference(avatar_split_clause,[],[f158,f144,f111,f91,f86,f162])).
% 0.18/0.49  fof(f91,plain,(
% 0.18/0.49    spl3_6 <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.18/0.49  fof(f144,plain,(
% 0.18/0.49    spl3_14 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.18/0.49  fof(f158,plain,(
% 0.18/0.49    sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1) | (~spl3_5 | spl3_6 | ~spl3_10 | ~spl3_14)),
% 0.18/0.49    inference(subsumption_resolution,[],[f157,f88])).
% 0.18/0.49  fof(f157,plain,(
% 0.18/0.49    sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl3_6 | ~spl3_10 | ~spl3_14)),
% 0.18/0.49    inference(subsumption_resolution,[],[f156,f112])).
% 0.18/0.49  fof(f156,plain,(
% 0.18/0.49    sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (spl3_6 | ~spl3_14)),
% 0.18/0.49    inference(superposition,[],[f93,f145])).
% 0.18/0.49  fof(f145,plain,(
% 0.18/0.49    ( ! [X2,X3] : (k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl3_14),
% 0.18/0.49    inference(avatar_component_clause,[],[f144])).
% 0.18/0.49  fof(f93,plain,(
% 0.18/0.49    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) | spl3_6),
% 0.18/0.49    inference(avatar_component_clause,[],[f91])).
% 0.18/0.49  fof(f155,plain,(
% 0.18/0.49    spl3_1 | ~spl3_2 | ~spl3_4 | spl3_15),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f154])).
% 0.18/0.49  fof(f154,plain,(
% 0.18/0.49    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | spl3_15)),
% 0.18/0.49    inference(subsumption_resolution,[],[f153,f72])).
% 0.18/0.49  fof(f153,plain,(
% 0.18/0.49    ~l3_lattices(sK0) | (spl3_1 | ~spl3_2 | spl3_15)),
% 0.18/0.49    inference(subsumption_resolution,[],[f152,f62])).
% 0.18/0.49  fof(f152,plain,(
% 0.18/0.49    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl3_1 | spl3_15)),
% 0.18/0.49    inference(subsumption_resolution,[],[f151,f57])).
% 0.18/0.49  fof(f151,plain,(
% 0.18/0.49    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl3_15),
% 0.18/0.49    inference(resolution,[],[f149,f36])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    ( ! [X0] : (v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f15])).
% 0.18/0.49  fof(f149,plain,(
% 0.18/0.49    ~v4_lattices(sK0) | spl3_15),
% 0.18/0.49    inference(avatar_component_clause,[],[f147])).
% 0.18/0.49  fof(f147,plain,(
% 0.18/0.49    spl3_15 <=> v4_lattices(sK0)),
% 0.18/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.18/0.49  fof(f150,plain,(
% 0.18/0.49    spl3_14 | ~spl3_15 | spl3_1 | ~spl3_8),
% 0.18/0.49    inference(avatar_split_clause,[],[f142,f99,f55,f147,f144])).
% 0.18/0.49  fof(f142,plain,(
% 0.18/0.49    ( ! [X2,X3] : (~v4_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3)) ) | (spl3_1 | ~spl3_8)),
% 0.18/0.49    inference(subsumption_resolution,[],[f75,f100])).
% 0.18/0.49  fof(f75,plain,(
% 0.18/0.49    ( ! [X2,X3] : (~v4_lattices(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X2,X3) = k3_lattices(sK0,X2,X3)) ) | spl3_1),
% 0.18/0.49    inference(resolution,[],[f57,f50])).
% 0.18/0.49  fof(f50,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_lattices(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f25])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.18/0.49    inference(flattening,[],[f24])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f6])).
% 0.18/0.49  fof(f6,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.18/0.49  fof(f141,plain,(
% 0.18/0.49    spl3_1 | ~spl3_2 | ~spl3_4 | spl3_13),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f140])).
% 0.18/0.49  fof(f140,plain,(
% 0.18/0.49    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | spl3_13)),
% 0.18/0.49    inference(subsumption_resolution,[],[f139,f72])).
% 0.18/0.49  fof(f139,plain,(
% 0.18/0.49    ~l3_lattices(sK0) | (spl3_1 | ~spl3_2 | spl3_13)),
% 0.18/0.49    inference(subsumption_resolution,[],[f138,f62])).
% 0.18/0.49  fof(f138,plain,(
% 0.18/0.49    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl3_1 | spl3_13)),
% 0.18/0.49    inference(subsumption_resolution,[],[f137,f57])).
% 0.18/0.49  fof(f137,plain,(
% 0.18/0.49    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl3_13),
% 0.18/0.49    inference(resolution,[],[f135,f38])).
% 0.18/0.49  fof(f38,plain,(
% 0.18/0.49    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f15])).
% 0.18/0.49  fof(f135,plain,(
% 0.18/0.49    ~v6_lattices(sK0) | spl3_13),
% 0.18/0.49    inference(avatar_component_clause,[],[f133])).
% 0.18/0.49  fof(f136,plain,(
% 0.18/0.49    spl3_12 | ~spl3_13 | spl3_1 | ~spl3_11),
% 0.18/0.49    inference(avatar_split_clause,[],[f128,f115,f55,f133,f130])).
% 0.18/0.49  fof(f128,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1)) ) | (spl3_1 | ~spl3_11)),
% 0.18/0.49    inference(subsumption_resolution,[],[f74,f116])).
% 0.18/0.49  fof(f74,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k4_lattices(sK0,X0,X1)) ) | spl3_1),
% 0.18/0.49    inference(resolution,[],[f57,f51])).
% 0.18/0.49  fof(f51,plain,(
% 0.18/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.18/0.49    inference(flattening,[],[f26])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ! [X0,X1,X2] : (k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f7])).
% 0.18/0.49  fof(f7,axiom,(
% 0.18/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k2_lattices(X0,X1,X2) = k4_lattices(X0,X1,X2))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.18/0.49  fof(f125,plain,(
% 0.18/0.49    spl3_1 | spl3_10 | ~spl3_11),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f124])).
% 0.18/0.49  fof(f124,plain,(
% 0.18/0.49    $false | (spl3_1 | spl3_10 | ~spl3_11)),
% 0.18/0.49    inference(subsumption_resolution,[],[f123,f57])).
% 0.18/0.49  fof(f123,plain,(
% 0.18/0.49    v2_struct_0(sK0) | (spl3_10 | ~spl3_11)),
% 0.18/0.49    inference(subsumption_resolution,[],[f122,f116])).
% 0.18/0.49  fof(f122,plain,(
% 0.18/0.49    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl3_10),
% 0.18/0.49    inference(resolution,[],[f113,f45])).
% 0.18/0.49  fof(f45,plain,(
% 0.18/0.49    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.18/0.49    inference(flattening,[],[f20])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.18/0.49  fof(f113,plain,(
% 0.18/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl3_10),
% 0.18/0.49    inference(avatar_component_clause,[],[f111])).
% 0.18/0.49  fof(f121,plain,(
% 0.18/0.49    ~spl3_4 | spl3_11),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f120])).
% 0.18/0.49  fof(f120,plain,(
% 0.18/0.49    $false | (~spl3_4 | spl3_11)),
% 0.18/0.49    inference(subsumption_resolution,[],[f119,f72])).
% 0.18/0.49  fof(f119,plain,(
% 0.18/0.49    ~l3_lattices(sK0) | spl3_11),
% 0.18/0.49    inference(resolution,[],[f117,f34])).
% 0.18/0.49  fof(f34,plain,(
% 0.18/0.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f13])).
% 0.18/0.49  fof(f13,plain,(
% 0.18/0.49    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.18/0.49    inference(ennf_transformation,[],[f5])).
% 0.18/0.49  fof(f5,axiom,(
% 0.18/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.18/0.49  fof(f117,plain,(
% 0.18/0.49    ~l1_lattices(sK0) | spl3_11),
% 0.18/0.49    inference(avatar_component_clause,[],[f115])).
% 0.18/0.49  fof(f105,plain,(
% 0.18/0.49    ~spl3_4 | spl3_8),
% 0.18/0.49    inference(avatar_contradiction_clause,[],[f104])).
% 0.18/0.49  fof(f104,plain,(
% 0.18/0.49    $false | (~spl3_4 | spl3_8)),
% 0.18/0.49    inference(subsumption_resolution,[],[f103,f72])).
% 0.18/0.49  fof(f103,plain,(
% 0.18/0.49    ~l3_lattices(sK0) | spl3_8),
% 0.18/0.49    inference(resolution,[],[f101,f35])).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f13])).
% 0.18/0.49  fof(f101,plain,(
% 0.18/0.49    ~l2_lattices(sK0) | spl3_8),
% 0.18/0.49    inference(avatar_component_clause,[],[f99])).
% 0.18/0.49  fof(f94,plain,(
% 0.18/0.49    ~spl3_6),
% 0.18/0.49    inference(avatar_split_clause,[],[f29,f91])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  fof(f12,plain,(
% 0.18/0.49    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.18/0.49    inference(flattening,[],[f11])).
% 0.18/0.49  fof(f11,plain,(
% 0.18/0.49    ? [X0] : (? [X1] : (k3_lattices(X0,k5_lattices(X0),X1) != X1 & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f10])).
% 0.18/0.49  fof(f10,negated_conjecture,(
% 0.18/0.49    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 0.18/0.49    inference(negated_conjecture,[],[f9])).
% 0.18/0.49  fof(f9,conjecture,(
% 0.18/0.49    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 0.18/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).
% 0.18/0.49  fof(f89,plain,(
% 0.18/0.49    spl3_5),
% 0.18/0.49    inference(avatar_split_clause,[],[f28,f86])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  fof(f73,plain,(
% 0.18/0.49    spl3_4),
% 0.18/0.49    inference(avatar_split_clause,[],[f33,f70])).
% 0.18/0.49  fof(f33,plain,(
% 0.18/0.49    l3_lattices(sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  fof(f68,plain,(
% 0.18/0.49    spl3_3),
% 0.18/0.49    inference(avatar_split_clause,[],[f32,f65])).
% 0.18/0.49  fof(f32,plain,(
% 0.18/0.49    v13_lattices(sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  fof(f63,plain,(
% 0.18/0.49    spl3_2),
% 0.18/0.49    inference(avatar_split_clause,[],[f31,f60])).
% 0.18/0.49  fof(f31,plain,(
% 0.18/0.49    v10_lattices(sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  fof(f58,plain,(
% 0.18/0.49    ~spl3_1),
% 0.18/0.49    inference(avatar_split_clause,[],[f30,f55])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    ~v2_struct_0(sK0)),
% 0.18/0.49    inference(cnf_transformation,[],[f12])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (9853)------------------------------
% 0.18/0.49  % (9853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (9853)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (9853)Memory used [KB]: 10746
% 0.18/0.49  % (9853)Time elapsed: 0.074 s
% 0.18/0.49  % (9853)------------------------------
% 0.18/0.49  % (9853)------------------------------
% 0.18/0.49  % (9859)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.18/0.49  % (9849)Success in time 0.15 s
%------------------------------------------------------------------------------
