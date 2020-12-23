%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 434 expanded)
%              Number of leaves         :   30 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  874 (1692 expanded)
%              Number of equality atoms :   60 ( 103 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f539,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f104,f108,f112,f116,f120,f124,f128,f132,f171,f254,f290,f307,f316,f333,f374,f530,f538])).

fof(f538,plain,
    ( spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | spl8_13
    | ~ spl8_24
    | ~ spl8_42 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | spl8_13
    | ~ spl8_24
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f536,f170])).

fof(f170,plain,
    ( sK1 != k15_lattice3(sK0,sK2)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl8_13
  <=> sK1 = k15_lattice3(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f536,plain,
    ( sK1 = k15_lattice3(sK0,sK2)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_24
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f532,f315])).

fof(f315,plain,
    ( sK1 = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl8_24
  <=> sK1 = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f532,plain,
    ( k15_lattice3(sK0,sK2) = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_42 ),
    inference(superposition,[],[f256,f529])).

fof(f529,plain,
    ( k15_lattice3(sK0,sK2) = k2_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl8_42
  <=> k15_lattice3(sK0,sK2) = k2_lattices(sK0,k15_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f256,plain,
    ( ! [X0] : k2_lattices(sK0,sK1,k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK1)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f154,f100])).

fof(f100,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f99,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f99,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f83,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f83,plain,
    ( l3_lattices(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl8_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1) )
    | spl8_1
    | ~ spl8_5
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f153,f103])).

fof(f103,plain,
    ( v6_lattices(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_5
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1)
        | ~ v6_lattices(sK0) )
    | spl8_1
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f152,f71])).

fof(f152,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1)
        | ~ v6_lattices(sK0) )
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f147,f123])).

fof(f123,plain,
    ( l1_lattices(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_10
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1)
        | ~ v6_lattices(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f127,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f127,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl8_11
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f530,plain,
    ( spl8_42
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f526,f372,f126,f114,f82,f70,f528])).

fof(f114,plain,
    ( spl8_8
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f372,plain,
    ( spl8_30
  <=> sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f526,plain,
    ( k15_lattice3(sK0,sK2) = k2_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_30 ),
    inference(superposition,[],[f474,f373])).

fof(f373,plain,
    ( sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f372])).

fof(f474,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),sK1))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(resolution,[],[f195,f127])).

% (19856)Termination reason: Refutation not found, incomplete strategy

% (19856)Memory used [KB]: 1791
% (19856)Time elapsed: 0.077 s
% (19856)------------------------------
% (19856)------------------------------
% (19858)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (19849)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (19854)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (19850)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (19852)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f195,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5)) )
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f194,f115])).

fof(f115,plain,
    ( v9_lattices(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f194,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5))
        | ~ v9_lattices(sK0) )
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f193,f71])).

fof(f193,plain,
    ( ! [X6,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5))
        | ~ v9_lattices(sK0) )
    | spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f178,f83])).

fof(f178,plain,
    ( ! [X6,X5] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5))
        | ~ v9_lattices(sK0) )
    | spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f100,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | ~ v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f374,plain,
    ( spl8_30
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f339,f331,f130,f126,f82,f70,f372])).

fof(f130,plain,
    ( spl8_12
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f331,plain,
    ( spl8_27
  <=> r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f339,plain,
    ( sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f338,f71])).

fof(f338,plain,
    ( sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f337,f127])).

fof(f337,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f336,f100])).

fof(f336,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f334,f131])).

fof(f131,plain,
    ( l2_lattices(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f334,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | v2_struct_0(sK0)
    | ~ spl8_27 ),
    inference(resolution,[],[f332,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f332,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f331])).

fof(f333,plain,
    ( spl8_27
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f327,f126,f118,f82,f78,f74,f70,f331])).

fof(f74,plain,
    ( spl8_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f78,plain,
    ( spl8_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f118,plain,
    ( spl8_9
  <=> r4_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f327,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f324,f127])).

fof(f324,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f185,f119])).

fof(f119,plain,
    ( r4_lattice3(sK0,sK1,sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f184,f71])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f183,f83])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f182,f79])).

fof(f79,plain,
    ( v4_lattice3(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f175,f75])).

fof(f75,plain,
    ( v10_lattices(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f100,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,X2,X3)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f316,plain,
    ( spl8_24
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f312,f305,f126,f114,f82,f70,f314])).

fof(f305,plain,
    ( spl8_22
  <=> k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f312,plain,
    ( sK1 = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_22 ),
    inference(superposition,[],[f263,f306])).

fof(f306,plain,
    ( k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f305])).

fof(f263,plain,
    ( ! [X0] : sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k15_lattice3(sK0,X0)))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(resolution,[],[f157,f100])).

fof(f157,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1)) )
    | spl8_1
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f156,f115])).

fof(f156,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1))
        | ~ v9_lattices(sK0) )
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f155,f71])).

fof(f155,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1))
        | ~ v9_lattices(sK0) )
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f148,f83])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1))
        | ~ v9_lattices(sK0) )
    | ~ spl8_11 ),
    inference(resolution,[],[f127,f56])).

fof(f307,plain,
    ( spl8_22
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f296,f288,f130,f126,f82,f70,f305])).

fof(f288,plain,
    ( spl8_19
  <=> r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f296,plain,
    ( k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f295,f71])).

fof(f295,plain,
    ( k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f294,f100])).

fof(f294,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f293,f127])).

fof(f293,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f291,f131])).

fof(f291,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f289,f53])).

fof(f289,plain,
    ( r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( spl8_19
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f272,f252,f126,f114,f110,f102,f82,f70,f288])).

fof(f110,plain,
    ( spl8_7
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f252,plain,
    ( spl8_16
  <=> r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f272,plain,
    ( r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f271,f71])).

fof(f271,plain,
    ( r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f270,f100])).

fof(f270,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f269,f127])).

fof(f269,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f268,f83])).

fof(f268,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f267,f115])).

fof(f267,plain,
    ( ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f266,f111])).

fof(f111,plain,
    ( v8_lattices(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f266,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f265,f103])).

fof(f265,plain,
    ( ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_16 ),
    inference(resolution,[],[f253,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f253,plain,
    ( r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl8_16
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f249,f126,f106,f82,f78,f74,f70,f252])).

fof(f106,plain,
    ( spl8_6
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f249,plain,
    ( r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(resolution,[],[f163,f107])).

fof(f107,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f163,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3)) )
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f162,f71])).

fof(f162,plain,
    ( ! [X3] :
        ( v2_struct_0(sK0)
        | ~ r2_hidden(sK1,X3)
        | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f161,f83])).

fof(f161,plain,
    ( ! [X3] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,X3)
        | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3)) )
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f160,f79])).

fof(f160,plain,
    ( ! [X3] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,X3)
        | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3)) )
    | ~ spl8_2
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f150,f75])).

fof(f150,plain,
    ( ! [X3] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ r2_hidden(sK1,X3)
        | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3)) )
    | ~ spl8_11 ),
    inference(resolution,[],[f127,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,X2)
      | r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f171,plain,(
    ~ spl8_13 ),
    inference(avatar_split_clause,[],[f36,f169])).

fof(f36,plain,(
    sK1 != k15_lattice3(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f132,plain,
    ( spl8_12
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f95,f82,f130])).

fof(f95,plain,
    ( l2_lattices(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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

fof(f128,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f37,f126])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,
    ( spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f94,f82,f122])).

fof(f94,plain,
    ( l1_lattices(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f120,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f35,f118])).

fof(f35,plain,(
    r4_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f116,plain,
    ( spl8_8
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f93,f82,f74,f70,f114])).

fof(f93,plain,
    ( v9_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f92,f83])).

fof(f92,plain,
    ( ~ l3_lattices(sK0)
    | v9_lattices(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f87,f71])).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v9_lattices(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

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

fof(f112,plain,
    ( spl8_7
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f91,f82,f74,f70,f110])).

fof(f91,plain,
    ( v8_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f90,f83])).

fof(f90,plain,
    ( ~ l3_lattices(sK0)
    | v8_lattices(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f86,f71])).

fof(f86,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v8_lattices(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f75,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f34,f106])).

fof(f34,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,
    ( spl8_5
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f89,f82,f74,f70,f102])).

fof(f89,plain,
    ( v6_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f88,f83])).

fof(f88,plain,
    ( ~ l3_lattices(sK0)
    | v6_lattices(sK0)
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f85,f71])).

fof(f85,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v6_lattices(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f75,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f38,f70])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (19848)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (19856)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (19855)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (19859)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (19851)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (19855)Refutation not found, incomplete strategy% (19855)------------------------------
% 0.22/0.50  % (19855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19855)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19855)Memory used [KB]: 6140
% 0.22/0.50  % (19855)Time elapsed: 0.002 s
% 0.22/0.50  % (19855)------------------------------
% 0.22/0.50  % (19855)------------------------------
% 0.22/0.50  % (19856)Refutation not found, incomplete strategy% (19856)------------------------------
% 0.22/0.50  % (19856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19863)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (19863)Refutation not found, incomplete strategy% (19863)------------------------------
% 0.22/0.50  % (19863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19863)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19863)Memory used [KB]: 10618
% 0.22/0.50  % (19863)Time elapsed: 0.080 s
% 0.22/0.50  % (19863)------------------------------
% 0.22/0.50  % (19863)------------------------------
% 0.22/0.51  % (19844)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (19843)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (19846)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (19845)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.52  % (19853)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (19857)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (19843)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f539,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f104,f108,f112,f116,f120,f124,f128,f132,f171,f254,f290,f307,f316,f333,f374,f530,f538])).
% 0.22/0.52  fof(f538,plain,(
% 0.22/0.52    spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | spl8_13 | ~spl8_24 | ~spl8_42),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f537])).
% 0.22/0.52  fof(f537,plain,(
% 0.22/0.52    $false | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | spl8_13 | ~spl8_24 | ~spl8_42)),
% 0.22/0.52    inference(subsumption_resolution,[],[f536,f170])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    sK1 != k15_lattice3(sK0,sK2) | spl8_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl8_13 <=> sK1 = k15_lattice3(sK0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.52  fof(f536,plain,(
% 0.22/0.52    sK1 = k15_lattice3(sK0,sK2) | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_24 | ~spl8_42)),
% 0.22/0.52    inference(forward_demodulation,[],[f532,f315])).
% 0.22/0.52  fof(f315,plain,(
% 0.22/0.52    sK1 = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | ~spl8_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f314])).
% 0.22/0.52  fof(f314,plain,(
% 0.22/0.52    spl8_24 <=> sK1 = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.52  fof(f532,plain,(
% 0.22/0.52    k15_lattice3(sK0,sK2) = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11 | ~spl8_42)),
% 0.22/0.52    inference(superposition,[],[f256,f529])).
% 0.22/0.52  fof(f529,plain,(
% 0.22/0.52    k15_lattice3(sK0,sK2) = k2_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | ~spl8_42),
% 0.22/0.52    inference(avatar_component_clause,[],[f528])).
% 0.22/0.52  fof(f528,plain,(
% 0.22/0.52    spl8_42 <=> k15_lattice3(sK0,sK2) = k2_lattices(sK0,k15_lattice3(sK0,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    ( ! [X0] : (k2_lattices(sK0,sK1,k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK1)) ) | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_10 | ~spl8_11)),
% 0.22/0.52    inference(resolution,[],[f154,f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl8_1 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f99,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ~v2_struct_0(sK0) | spl8_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl8_1 <=> v2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK0) | m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | ~spl8_4),
% 0.22/0.52    inference(resolution,[],[f83,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    l3_lattices(sK0) | ~spl8_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl8_4 <=> l3_lattices(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1)) ) | (spl8_1 | ~spl8_5 | ~spl8_10 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f153,f103])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    v6_lattices(sK0) | ~spl8_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f102])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    spl8_5 <=> v6_lattices(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1) | ~v6_lattices(sK0)) ) | (spl8_1 | ~spl8_10 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f152,f71])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1) | ~v6_lattices(sK0)) ) | (~spl8_10 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f147,f123])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    l1_lattices(sK0) | ~spl8_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f122])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl8_10 <=> l1_lattices(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,sK1,X0) = k2_lattices(sK0,X0,sK1) | ~v6_lattices(sK0)) ) | ~spl8_11),
% 0.22/0.52    inference(resolution,[],[f127,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~v6_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f126])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    spl8_11 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.52  fof(f530,plain,(
% 0.22/0.52    spl8_42 | spl8_1 | ~spl8_4 | ~spl8_8 | ~spl8_11 | ~spl8_30),
% 0.22/0.52    inference(avatar_split_clause,[],[f526,f372,f126,f114,f82,f70,f528])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl8_8 <=> v9_lattices(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.52  fof(f372,plain,(
% 0.22/0.52    spl8_30 <=> sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.22/0.52  fof(f526,plain,(
% 0.22/0.52    k15_lattice3(sK0,sK2) = k2_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | (spl8_1 | ~spl8_4 | ~spl8_8 | ~spl8_11 | ~spl8_30)),
% 0.22/0.52    inference(superposition,[],[f474,f373])).
% 0.22/0.52  fof(f373,plain,(
% 0.22/0.52    sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | ~spl8_30),
% 0.22/0.52    inference(avatar_component_clause,[],[f372])).
% 0.22/0.52  fof(f474,plain,(
% 0.22/0.52    ( ! [X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k1_lattices(sK0,k15_lattice3(sK0,X0),sK1))) ) | (spl8_1 | ~spl8_4 | ~spl8_8 | ~spl8_11)),
% 0.22/0.52    inference(resolution,[],[f195,f127])).
% 0.22/0.52  % (19856)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19856)Memory used [KB]: 1791
% 0.22/0.52  % (19856)Time elapsed: 0.077 s
% 0.22/0.52  % (19856)------------------------------
% 0.22/0.52  % (19856)------------------------------
% 0.22/0.52  % (19858)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (19849)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (19854)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (19850)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (19852)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5))) ) | (spl8_1 | ~spl8_4 | ~spl8_8)),
% 0.22/0.52    inference(subsumption_resolution,[],[f194,f115])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    v9_lattices(sK0) | ~spl8_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f114])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5)) | ~v9_lattices(sK0)) ) | (spl8_1 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f193,f71])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ( ! [X6,X5] : (v2_struct_0(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5)) | ~v9_lattices(sK0)) ) | (spl8_1 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f178,f83])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    ( ! [X6,X5] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k1_lattices(sK0,k15_lattice3(sK0,X6),X5)) | ~v9_lattices(sK0)) ) | (spl8_1 | ~spl8_4)),
% 0.22/0.52    inference(resolution,[],[f100,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~v9_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 0.22/0.52  fof(f374,plain,(
% 0.22/0.52    spl8_30 | spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_12 | ~spl8_27),
% 0.22/0.52    inference(avatar_split_clause,[],[f339,f331,f130,f126,f82,f70,f372])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    spl8_12 <=> l2_lattices(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.52  fof(f331,plain,(
% 0.22/0.52    spl8_27 <=> r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.22/0.52  fof(f339,plain,(
% 0.22/0.52    sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | (spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_12 | ~spl8_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f338,f71])).
% 0.22/0.52  fof(f338,plain,(
% 0.22/0.52    sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | (spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_12 | ~spl8_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f337,f127])).
% 0.22/0.52  fof(f337,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | (spl8_1 | ~spl8_4 | ~spl8_12 | ~spl8_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f336,f100])).
% 0.22/0.52  fof(f336,plain,(
% 0.22/0.52    ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f334,f131])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    l2_lattices(sK0) | ~spl8_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f130])).
% 0.22/0.52  fof(f334,plain,(
% 0.22/0.52    ~l2_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | v2_struct_0(sK0) | ~spl8_27),
% 0.22/0.52    inference(resolution,[],[f332,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.22/0.52  fof(f332,plain,(
% 0.22/0.52    r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | ~spl8_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f331])).
% 0.22/0.52  fof(f333,plain,(
% 0.22/0.52    spl8_27 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f327,f126,f118,f82,f78,f74,f70,f331])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl8_2 <=> v10_lattices(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl8_3 <=> v4_lattice3(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl8_9 <=> r4_lattice3(sK0,sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.52  fof(f327,plain,(
% 0.22/0.52    r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f324,f127])).
% 0.22/0.52  fof(f324,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,sK2),sK1) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.22/0.52    inference(resolution,[],[f185,f119])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    r4_lattice3(sK0,sK1,sK2) | ~spl8_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f184,f71])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f183,f83])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f182,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    v4_lattice3(sK0) | ~spl8_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f78])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    v10_lattices(sK0) | ~spl8_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f74])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl8_1 | ~spl8_4)),
% 0.22/0.52    inference(resolution,[],[f100,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,k15_lattice3(X0,X1),X3)) )),
% 0.22/0.52    inference(equality_resolution,[],[f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,X2,X3) | k15_lattice3(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 0.22/0.52  fof(f316,plain,(
% 0.22/0.52    spl8_24 | spl8_1 | ~spl8_4 | ~spl8_8 | ~spl8_11 | ~spl8_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f312,f305,f126,f114,f82,f70,f314])).
% 0.22/0.52  fof(f305,plain,(
% 0.22/0.52    spl8_22 <=> k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.52  fof(f312,plain,(
% 0.22/0.52    sK1 = k2_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | (spl8_1 | ~spl8_4 | ~spl8_8 | ~spl8_11 | ~spl8_22)),
% 0.22/0.52    inference(superposition,[],[f263,f306])).
% 0.22/0.52  fof(f306,plain,(
% 0.22/0.52    k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | ~spl8_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f305])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k15_lattice3(sK0,X0)))) ) | (spl8_1 | ~spl8_4 | ~spl8_8 | ~spl8_11)),
% 0.22/0.52    inference(resolution,[],[f157,f100])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1))) ) | (spl8_1 | ~spl8_4 | ~spl8_8 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f156,f115])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1)) | ~v9_lattices(sK0)) ) | (spl8_1 | ~spl8_4 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f155,f71])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1)) | ~v9_lattices(sK0)) ) | (~spl8_4 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f148,f83])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ( ! [X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X1)) | ~v9_lattices(sK0)) ) | ~spl8_11),
% 0.22/0.52    inference(resolution,[],[f127,f56])).
% 0.22/0.52  fof(f307,plain,(
% 0.22/0.52    spl8_22 | spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_12 | ~spl8_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f296,f288,f130,f126,f82,f70,f305])).
% 0.22/0.52  fof(f288,plain,(
% 0.22/0.52    spl8_19 <=> r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | (spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_12 | ~spl8_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f295,f71])).
% 0.22/0.52  fof(f295,plain,(
% 0.22/0.52    k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_4 | ~spl8_11 | ~spl8_12 | ~spl8_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f294,f100])).
% 0.22/0.52  fof(f294,plain,(
% 0.22/0.52    ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_11 | ~spl8_12 | ~spl8_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f293,f127])).
% 0.22/0.52  fof(f293,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_12 | ~spl8_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f291,f131])).
% 0.22/0.52  fof(f291,plain,(
% 0.22/0.52    ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | k15_lattice3(sK0,sK2) = k1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~spl8_19),
% 0.22/0.52    inference(resolution,[],[f289,f53])).
% 0.22/0.52  fof(f289,plain,(
% 0.22/0.52    r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | ~spl8_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f288])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    spl8_19 | spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f272,f252,f126,f114,f110,f102,f82,f70,f288])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    spl8_7 <=> v8_lattices(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.52  fof(f252,plain,(
% 0.22/0.52    spl8_16 <=> r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.52  fof(f272,plain,(
% 0.22/0.52    r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f271,f71])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f270,f100])).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_11 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f269,f127])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f268,f83])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_7 | ~spl8_8 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f267,f115])).
% 0.22/0.52  fof(f267,plain,(
% 0.22/0.52    ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_7 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f266,f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    v8_lattices(sK0) | ~spl8_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f110])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_16)),
% 0.22/0.52    inference(subsumption_resolution,[],[f265,f103])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,sK2),u1_struct_0(sK0)) | r1_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | v2_struct_0(sK0) | ~spl8_16),
% 0.22/0.52    inference(resolution,[],[f253,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | ~spl8_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f252])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    spl8_16 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f249,f126,f106,f82,f78,f74,f70,f252])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl8_6 <=> r2_hidden(sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.52  fof(f249,plain,(
% 0.22/0.52    r3_lattices(sK0,sK1,k15_lattice3(sK0,sK2)) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_6 | ~spl8_11)),
% 0.22/0.52    inference(resolution,[],[f163,f107])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    r2_hidden(sK1,sK2) | ~spl8_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f106])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(sK1,X3) | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3))) ) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f162,f71])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X3] : (v2_struct_0(sK0) | ~r2_hidden(sK1,X3) | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3))) ) | (~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f161,f83])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ( ! [X3] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK1,X3) | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3))) ) | (~spl8_2 | ~spl8_3 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f160,f79])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ( ! [X3] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK1,X3) | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3))) ) | (~spl8_2 | ~spl8_11)),
% 0.22/0.52    inference(subsumption_resolution,[],[f150,f75])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X3] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~r2_hidden(sK1,X3) | r3_lattices(sK0,sK1,k15_lattice3(sK0,X3))) ) | ~spl8_11),
% 0.22/0.52    inference(resolution,[],[f127,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~r2_hidden(X1,X2) | r3_lattices(X0,X1,k15_lattice3(X0,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ~spl8_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f36,f169])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    sK1 != k15_lattice3(sK0,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & (r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    spl8_12 | ~spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f95,f82,f130])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    l2_lattices(sK0) | ~spl8_4),
% 0.22/0.52    inference(resolution,[],[f83,f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl8_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f37,f126])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl8_10 | ~spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f94,f82,f122])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    l1_lattices(sK0) | ~spl8_4),
% 0.22/0.52    inference(resolution,[],[f83,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    spl8_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f35,f118])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    r4_lattice3(sK0,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    spl8_8 | spl8_1 | ~spl8_2 | ~spl8_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f93,f82,f74,f70,f114])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    v9_lattices(sK0) | (spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f92,f83])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ~l3_lattices(sK0) | v9_lattices(sK0) | (spl8_1 | ~spl8_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f87,f71])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    v2_struct_0(sK0) | ~l3_lattices(sK0) | v9_lattices(sK0) | ~spl8_2),
% 0.22/0.52    inference(resolution,[],[f75,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v9_lattices(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl8_7 | spl8_1 | ~spl8_2 | ~spl8_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f91,f82,f74,f70,f110])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    v8_lattices(sK0) | (spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f90,f83])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~l3_lattices(sK0) | v8_lattices(sK0) | (spl8_1 | ~spl8_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f86,f71])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~l3_lattices(sK0) | v8_lattices(sK0) | ~spl8_2),
% 0.22/0.53    inference(resolution,[],[f75,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v8_lattices(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl8_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f106])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl8_5 | spl8_1 | ~spl8_2 | ~spl8_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f89,f82,f74,f70,f102])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    v6_lattices(sK0) | (spl8_1 | ~spl8_2 | ~spl8_4)),
% 0.22/0.53    inference(subsumption_resolution,[],[f88,f83])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~l3_lattices(sK0) | v6_lattices(sK0) | (spl8_1 | ~spl8_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f85,f71])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    v2_struct_0(sK0) | ~l3_lattices(sK0) | v6_lattices(sK0) | ~spl8_2),
% 0.22/0.53    inference(resolution,[],[f75,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl8_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f82])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    l3_lattices(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl8_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f78])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    v4_lattice3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    spl8_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f74])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v10_lattices(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ~spl8_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f70])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (19843)------------------------------
% 0.22/0.53  % (19843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19843)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (19843)Memory used [KB]: 6396
% 0.22/0.53  % (19843)Time elapsed: 0.094 s
% 0.22/0.53  % (19843)------------------------------
% 0.22/0.53  % (19843)------------------------------
% 0.22/0.53  % (19842)Success in time 0.164 s
%------------------------------------------------------------------------------
