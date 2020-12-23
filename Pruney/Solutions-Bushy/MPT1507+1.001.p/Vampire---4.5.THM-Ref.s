%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1507+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 302 expanded)
%              Number of leaves         :   30 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          :  828 (1632 expanded)
%              Number of equality atoms :   50 ( 135 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f104,f109,f122,f130,f150,f167,f179,f186,f191,f222,f229,f244,f257])).

fof(f257,plain,
    ( ~ spl4_5
    | ~ spl4_7
    | spl4_8
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_7
    | spl4_8
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f255,f103])).

fof(f103,plain,
    ( r4_lattice3(sK0,sK1,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f101])).

% (12273)Refutation not found, incomplete strategy% (12273)------------------------------
% (12273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12273)Termination reason: Refutation not found, incomplete strategy

% (12273)Memory used [KB]: 10618
% (12273)Time elapsed: 0.093 s
% (12273)------------------------------
% (12273)------------------------------
fof(f101,plain,
    ( spl4_7
  <=> r4_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f255,plain,
    ( ~ r4_lattice3(sK0,sK1,sK2)
    | ~ spl4_5
    | spl4_8
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f253,f108])).

fof(f108,plain,
    ( sK1 != k15_lattice3(sK0,sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_8
  <=> sK1 = k15_lattice3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f253,plain,
    ( sK1 = k15_lattice3(sK0,sK2)
    | ~ r4_lattice3(sK0,sK1,sK2)
    | ~ spl4_5
    | ~ spl4_23 ),
    inference(resolution,[],[f243,f93])).

fof(f93,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_5
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | sK1 = k15_lattice3(sK0,X0)
        | ~ r4_lattice3(sK0,sK1,X0) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl4_23
  <=> ! [X0] :
        ( ~ r4_lattice3(sK0,sK1,X0)
        | sK1 = k15_lattice3(sK0,X0)
        | ~ r2_hidden(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f244,plain,
    ( spl4_23
    | spl4_1
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f236,f227,f86,f71,f242])).

fof(f71,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f86,plain,
    ( spl4_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f227,plain,
    ( spl4_20
  <=> ! [X2] :
        ( k15_lattice3(sK0,X2) = sK1
        | ~ r4_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK0,sK1,X0)
        | sK1 = k15_lattice3(sK0,X0)
        | ~ r2_hidden(sK1,X0) )
    | spl4_1
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f235,f73])).

fof(f73,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK0,sK1,X0)
        | sK1 = k15_lattice3(sK0,X0)
        | ~ r2_hidden(sK1,X0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f234,f88])).

fof(f88,plain,
    ( l3_lattices(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK0,sK1,X0)
        | sK1 = k15_lattice3(sK0,X0)
        | ~ r2_hidden(sK1,X0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_20 ),
    inference(resolution,[],[f228,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f228,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,sK1,X2)
        | k15_lattice3(sK0,X2) = sK1
        | ~ r2_hidden(sK1,X2) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl4_20
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f225,f220,f165,f96,f227])).

fof(f96,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f165,plain,
    ( spl4_13
  <=> ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f220,plain,
    ( spl4_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | k15_lattice3(sK0,X1) = X0
        | ~ r4_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f225,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,X2) = sK1
        | ~ r4_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X2) )
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f224,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f224,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | k15_lattice3(sK0,X2) = sK1
        | ~ r4_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X2) )
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(resolution,[],[f221,f166])).

fof(f166,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X0
        | ~ r4_lattice3(sK0,X0,X1) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f220])).

fof(f222,plain,
    ( spl4_19
    | spl4_1
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f200,f177,f86,f71,f220])).

fof(f177,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | k15_lattice3(sK0,X1) = X0
        | ~ r4_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

% (12274)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | k15_lattice3(sK0,X1) = X0
        | ~ r4_lattice3(sK0,X0,X1) )
    | spl4_1
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f199,f73])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | k15_lattice3(sK0,X1) = X0
        | ~ r4_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f198,f88])).

% (12279)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | k15_lattice3(sK0,X1) = X0
        | ~ r4_lattice3(sK0,X0,X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_16 ),
    inference(resolution,[],[f178,f60])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | k15_lattice3(sK0,X1) = X0
        | ~ r4_lattice3(sK0,X0,X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f191,plain,
    ( ~ spl4_4
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl4_4
    | spl4_15 ),
    inference(subsumption_resolution,[],[f188,f88])).

fof(f188,plain,
    ( ~ l3_lattices(sK0)
    | spl4_15 ),
    inference(resolution,[],[f175,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f175,plain,
    ( ~ l2_lattices(sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_15
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f186,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_14 ),
    inference(subsumption_resolution,[],[f184,f88])).

fof(f184,plain,
    ( ~ l3_lattices(sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_14 ),
    inference(subsumption_resolution,[],[f183,f73])).

fof(f183,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl4_2
    | spl4_14 ),
    inference(subsumption_resolution,[],[f181,f78])).

fof(f78,plain,
    ( v10_lattices(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f181,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_14 ),
    inference(resolution,[],[f171,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f171,plain,
    ( ~ v4_lattices(sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl4_14
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f179,plain,
    ( ~ spl4_14
    | ~ spl4_15
    | spl4_16
    | spl4_1
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f133,f128,f71,f177,f173,f169])).

fof(f128,plain,
    ( spl4_10
  <=> ! [X1,X0] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k15_lattice3(sK0,X1) = X0
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | ~ v4_lattices(sK0) )
    | spl4_1
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f132,f73])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k15_lattice3(sK0,X1) = X0
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_10 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k15_lattice3(sK0,X1) = X0
        | ~ r1_lattices(sK0,X0,k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f129,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f129,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f167,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f162,f148,f96,f86,f81,f76,f71,f165])).

fof(f81,plain,
    ( spl4_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

% (12275)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f148,plain,
    ( spl4_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK1,X0)
        | ~ r3_lattices(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f162,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f161,f73])).

fof(f161,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f160,f78])).

fof(f160,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f159,f83])).

fof(f83,plain,
    ( v4_lattice3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f159,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f158,f88])).

fof(f158,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f155,f98])).

fof(f155,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK1,k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f149,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r3_lattices(sK0,sK1,X0)
        | r1_lattices(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( spl4_11
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f134,f120,f96,f148])).

fof(f120,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,X0)
        | ~ r3_lattices(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK1,X0)
        | ~ r3_lattices(sK0,sK1,X0) )
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(resolution,[],[f121,f98])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,X0)
        | ~ r3_lattices(sK0,X1,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f130,plain,
    ( spl4_10
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f126,f86,f81,f76,f71,f128])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f125,f73])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f124,f78])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f123,f88])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f118,f83])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f66,f60])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK3(X0,X1,X2))
                & r4_lattice3(X0,sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK3(X0,X1,X2))
        & r4_lattice3(X0,sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f122,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f117,f86,f76,f71,f120])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,X0)
        | ~ r3_lattices(sK0,X1,X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f116,f73])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,X1,X0)
        | v2_struct_0(sK0)
        | ~ r3_lattices(sK0,X1,X0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f115,f88])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X1,X0)
        | v2_struct_0(sK0)
        | ~ r3_lattices(sK0,X1,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f114,f78])).

% (12290)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (12277)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f112,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f109,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    sK1 != k15_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k15_lattice3(sK0,sK2)
    & r4_lattice3(sK0,sK1,sK2)
    & r2_hidden(sK1,sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k15_lattice3(X0,X2) != X1
                & r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(sK0,X2) != X1
              & r4_lattice3(sK0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k15_lattice3(sK0,X2) != X1
            & r4_lattice3(sK0,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k15_lattice3(sK0,X2) != sK1
          & r4_lattice3(sK0,sK1,X2)
          & r2_hidden(sK1,X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( k15_lattice3(sK0,X2) != sK1
        & r4_lattice3(sK0,sK1,X2)
        & r2_hidden(sK1,X2) )
   => ( sK1 != k15_lattice3(sK0,sK2)
      & r4_lattice3(sK0,sK1,sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r4_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k15_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

fof(f104,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    r4_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f36,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
