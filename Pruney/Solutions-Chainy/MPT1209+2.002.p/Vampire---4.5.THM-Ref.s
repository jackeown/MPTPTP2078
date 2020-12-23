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
% DateTime   : Thu Dec  3 13:10:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 246 expanded)
%              Number of leaves         :   22 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  430 (1032 expanded)
%              Number of equality atoms :   41 ( 112 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f90,f99,f108,f130,f132,f137,f142,f160,f174,f179,f184,f191,f238])).

fof(f238,plain,
    ( ~ spl2_16
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(trivial_inequality_removal,[],[f236])).

fof(f236,plain,
    ( k6_lattices(sK0) != k6_lattices(sK0)
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(superposition,[],[f33,f233])).

fof(f233,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl2_16
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f157,f232])).

fof(f232,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f165,f170])).

fof(f170,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl2_18
  <=> k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f165,plain,
    ( k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl2_17
  <=> k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f157,plain,
    ( k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl2_16
  <=> k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f33,plain,(
    k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_lattices)).

fof(f191,plain,
    ( spl2_16
    | ~ spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f190,f56,f111,f156])).

fof(f111,plain,
    ( spl2_10
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f56,plain,
    ( spl2_1
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f190,plain,
    ( ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(global_subsumption,[],[f34,f187])).

fof(f187,plain,
    ( ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f105,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l2_lattices(X2)
      | ~ v4_lattices(X2)
      | v2_struct_0(X2)
      | k3_lattices(X2,X1,k6_lattices(X2)) = k3_lattices(X2,k6_lattices(X2),X1) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l2_lattices(X2)
      | ~ v4_lattices(X2)
      | v2_struct_0(X2)
      | k3_lattices(X2,X1,k6_lattices(X2)) = k3_lattices(X2,k6_lattices(X2),X1)
      | ~ l2_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

% (2174)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (2190)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f184,plain,
    ( spl2_17
    | ~ spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f183,f56,f111,f164])).

fof(f183,plain,
    ( ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(global_subsumption,[],[f34,f180])).

fof(f180,plain,
    ( ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    inference(resolution,[],[f97,f32])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l2_lattices(X2)
      | ~ v4_lattices(X2)
      | v2_struct_0(X2)
      | k3_lattices(X2,X1,k6_lattices(X2)) = k1_lattices(X2,X1,k6_lattices(X2)) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l2_lattices(X2)
      | ~ v4_lattices(X2)
      | v2_struct_0(X2)
      | k3_lattices(X2,X1,k6_lattices(X2)) = k1_lattices(X2,X1,k6_lattices(X2))
      | ~ l2_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f47,f44])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
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
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f179,plain,(
    spl2_19 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl2_19 ),
    inference(resolution,[],[f173,f32])).

% (2174)Refutation not found, incomplete strategy% (2174)------------------------------
% (2174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2174)Termination reason: Refutation not found, incomplete strategy

% (2174)Memory used [KB]: 6140
% (2174)Time elapsed: 0.055 s
% (2174)------------------------------
% (2174)------------------------------
fof(f173,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl2_19
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f174,plain,
    ( spl2_9
    | spl2_18
    | ~ spl2_3
    | ~ spl2_19
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f167,f77,f56,f172,f68,f169,f88])).

fof(f88,plain,
    ( spl2_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f68,plain,
    ( spl2_3
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f77,plain,
    ( spl2_6
  <=> r1_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f167,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f78,f46])).

% (2176)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (2175)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

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

% (2189)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f78,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f160,plain,
    ( spl2_9
    | ~ spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f159,f68,f56,f88])).

fof(f159,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | spl2_3 ),
    inference(resolution,[],[f69,f44])).

fof(f69,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f142,plain,(
    ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl2_9 ),
    inference(resolution,[],[f89,f34])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f137,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f86,f35])).

fof(f35,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,
    ( ~ v10_lattices(sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_8
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f132,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f83,f37])).

fof(f37,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,
    ( ~ l3_lattices(sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_7
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f130,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_9
    | spl2_10 ),
    inference(avatar_split_clause,[],[f129,f111,f88,f85,f82])).

fof(f129,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl2_10 ),
    inference(resolution,[],[f112,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
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
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
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
    ( ~ v4_lattices(sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f108,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f62,f37])).

fof(f62,plain,
    ( ~ l3_lattices(sK0)
    | spl2_1 ),
    inference(resolution,[],[f57,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

% (2175)Refutation not found, incomplete strategy% (2175)------------------------------
% (2175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2175)Termination reason: Refutation not found, incomplete strategy

% (2175)Memory used [KB]: 10618
% (2175)Time elapsed: 0.093 s
% (2175)------------------------------
% (2175)------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

% (2191)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f57,plain,
    ( ~ l2_lattices(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f99,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_9
    | spl2_5 ),
    inference(avatar_split_clause,[],[f98,f74,f88,f85,f82])).

fof(f74,plain,
    ( spl2_5
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f98,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl2_5 ),
    inference(resolution,[],[f75,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,
    ( ~ v6_lattices(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f90,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_9
    | spl2_4 ),
    inference(avatar_split_clause,[],[f80,f71,f88,f85,f82])).

fof(f71,plain,
    ( spl2_4
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f80,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl2_4 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

% (2173)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f72,plain,
    ( ~ v8_lattices(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f79,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f66,f77,f74,f71,f68])).

fof(f66,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f34,f37,f32,f64])).

fof(f64,plain,
    ( r1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ v6_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f42,f52])).

fof(f52,plain,(
    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(global_subsumption,[],[f34,f35,f36,f37,f49])).

fof(f49,plain,
    ( ~ v10_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).

fof(f36,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

% (2189)Refutation not found, incomplete strategy% (2189)------------------------------
% (2189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2189)Termination reason: Refutation not found, incomplete strategy

% (2189)Memory used [KB]: 1663
% (2189)Time elapsed: 0.095 s
% (2189)------------------------------
% (2189)------------------------------
fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (2188)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (2171)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (2167)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (2169)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (2172)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (2188)Refutation not found, incomplete strategy% (2188)------------------------------
% 0.21/0.50  % (2188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2179)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (2188)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (2188)Memory used [KB]: 6012
% 0.21/0.50  % (2188)Time elapsed: 0.095 s
% 0.21/0.50  % (2188)------------------------------
% 0.21/0.50  % (2188)------------------------------
% 0.21/0.50  % (2170)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (2183)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (2180)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (2179)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f79,f90,f99,f108,f130,f132,f137,f142,f160,f174,f179,f184,f191,f238])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ~spl2_16 | ~spl2_17 | ~spl2_18),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    $false | (~spl2_16 | ~spl2_17 | ~spl2_18)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f236])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    k6_lattices(sK0) != k6_lattices(sK0) | (~spl2_16 | ~spl2_17 | ~spl2_18)),
% 0.21/0.51    inference(superposition,[],[f33,f233])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1) | (~spl2_16 | ~spl2_17 | ~spl2_18)),
% 0.21/0.51    inference(backward_demodulation,[],[f157,f232])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | (~spl2_17 | ~spl2_18)),
% 0.21/0.51    inference(forward_demodulation,[],[f165,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~spl2_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl2_18 <=> k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | ~spl2_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl2_17 <=> k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | ~spl2_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl2_16 <=> k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_lattices)).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl2_16 | ~spl2_10 | ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f190,f56,f111,f156])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl2_10 <=> v4_lattices(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl2_1 <=> l2_lattices(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(global_subsumption,[],[f34,f187])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(resolution,[],[f105,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(X2)) | ~l2_lattices(X2) | ~v4_lattices(X2) | v2_struct_0(X2) | k3_lattices(X2,X1,k6_lattices(X2)) = k3_lattices(X2,k6_lattices(X2),X1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(X2)) | ~l2_lattices(X2) | ~v4_lattices(X2) | v2_struct_0(X2) | k3_lattices(X2,X1,k6_lattices(X2)) = k3_lattices(X2,k6_lattices(X2),X1) | ~l2_lattices(X2) | v2_struct_0(X2)) )),
% 0.21/0.51    inference(resolution,[],[f48,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  % (2174)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  % (2190)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    spl2_17 | ~spl2_10 | ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f183,f56,f111,f164])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~v4_lattices(sK0) | k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(global_subsumption,[],[f34,f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | k3_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    inference(resolution,[],[f97,f32])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(X2)) | ~l2_lattices(X2) | ~v4_lattices(X2) | v2_struct_0(X2) | k3_lattices(X2,X1,k6_lattices(X2)) = k1_lattices(X2,X1,k6_lattices(X2))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(X2)) | ~l2_lattices(X2) | ~v4_lattices(X2) | v2_struct_0(X2) | k3_lattices(X2,X1,k6_lattices(X2)) = k1_lattices(X2,X1,k6_lattices(X2)) | ~l2_lattices(X2) | v2_struct_0(X2)) )),
% 0.21/0.51    inference(resolution,[],[f47,f44])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl2_19),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    $false | spl2_19),
% 0.21/0.51    inference(resolution,[],[f173,f32])).
% 0.21/0.51  % (2174)Refutation not found, incomplete strategy% (2174)------------------------------
% 0.21/0.51  % (2174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2174)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2174)Memory used [KB]: 6140
% 0.21/0.51  % (2174)Time elapsed: 0.055 s
% 0.21/0.51  % (2174)------------------------------
% 0.21/0.51  % (2174)------------------------------
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl2_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    spl2_19 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl2_9 | spl2_18 | ~spl2_3 | ~spl2_19 | ~spl2_1 | ~spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f167,f77,f56,f172,f68,f169,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl2_9 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl2_3 <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl2_6 <=> r1_lattices(sK0,sK1,k6_lattices(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0)) | v2_struct_0(sK0) | ~spl2_6),
% 0.21/0.51    inference(resolution,[],[f78,f46])).
% 0.21/0.51  % (2176)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  % (2175)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.51  % (2189)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl2_9 | ~spl2_1 | spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f159,f68,f56,f88])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | v2_struct_0(sK0) | spl2_3),
% 0.21/0.51    inference(resolution,[],[f69,f44])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ~spl2_9),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    $false | ~spl2_9),
% 0.21/0.51    inference(resolution,[],[f89,f34])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl2_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    $false | spl2_8),
% 0.21/0.51    inference(resolution,[],[f86,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v10_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~v10_lattices(sK0) | spl2_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl2_8 <=> v10_lattices(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl2_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    $false | spl2_7),
% 0.21/0.51    inference(resolution,[],[f83,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    l3_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~l3_lattices(sK0) | spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl2_7 <=> l3_lattices(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~spl2_7 | ~spl2_8 | spl2_9 | spl2_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f129,f111,f88,f85,f82])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl2_10),
% 0.21/0.51    inference(resolution,[],[f112,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (((v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~v4_lattices(sK0) | spl2_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f111])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    $false | spl2_1),
% 0.21/0.51    inference(resolution,[],[f62,f37])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ~l3_lattices(sK0) | spl2_1),
% 0.21/0.51    inference(resolution,[],[f57,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.51  % (2175)Refutation not found, incomplete strategy% (2175)------------------------------
% 0.21/0.51  % (2175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2175)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2175)Memory used [KB]: 10618
% 0.21/0.51  % (2175)Time elapsed: 0.093 s
% 0.21/0.51  % (2175)------------------------------
% 0.21/0.51  % (2175)------------------------------
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.51  % (2191)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~l2_lattices(sK0) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f56])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ~spl2_7 | ~spl2_8 | spl2_9 | spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f98,f74,f88,f85,f82])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl2_5 <=> v6_lattices(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl2_5),
% 0.21/0.51    inference(resolution,[],[f75,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ~v6_lattices(sK0) | spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ~spl2_7 | ~spl2_8 | spl2_9 | spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f80,f71,f88,f85,f82])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl2_4 <=> v8_lattices(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl2_4),
% 0.21/0.51    inference(resolution,[],[f72,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  % (2173)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ~v8_lattices(sK0) | spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f77,f74,f71,f68])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.51    inference(global_subsumption,[],[f34,f37,f32,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    r1_lattices(sK0,sK1,k6_lattices(sK0)) | ~v6_lattices(sK0) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.51    inference(superposition,[],[f42,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.21/0.51    inference(global_subsumption,[],[f34,f35,f36,f37,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~v10_lattices(sK0) | ~v14_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 0.21/0.51    inference(resolution,[],[f43,f32])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v14_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k4_lattices(X0,k6_lattices(X0),X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattices)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v14_lattices(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  % (2189)Refutation not found, incomplete strategy% (2189)------------------------------
% 0.21/0.51  % (2189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2189)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2189)Memory used [KB]: 1663
% 0.21/0.51  % (2189)Time elapsed: 0.095 s
% 0.21/0.51  % (2189)------------------------------
% 0.21/0.51  % (2189)------------------------------
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (2179)------------------------------
% 0.21/0.51  % (2179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2179)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (2179)Memory used [KB]: 10746
% 0.21/0.51  % (2179)Time elapsed: 0.112 s
% 0.21/0.51  % (2179)------------------------------
% 0.21/0.51  % (2179)------------------------------
% 0.21/0.51  % (2168)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (2191)Refutation not found, incomplete strategy% (2191)------------------------------
% 0.21/0.52  % (2191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2182)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (2164)Success in time 0.157 s
%------------------------------------------------------------------------------
