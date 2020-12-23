%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1222+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 146 expanded)
%              Number of leaves         :   16 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  219 ( 485 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14821)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
fof(f2883,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2245,f2248,f2252,f2256,f2288,f2293,f2495,f2496,f2733,f2862,f2868,f2882])).

fof(f2882,plain,
    ( spl11_9
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f2881,f2291,f2282,f2254,f2240,f2286])).

fof(f2286,plain,
    ( spl11_9
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f2240,plain,
    ( spl11_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f2254,plain,
    ( spl11_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f2282,plain,
    ( spl11_8
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f2291,plain,
    ( spl11_10
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f2881,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f2880,f2292])).

fof(f2292,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f2291])).

fof(f2880,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f2878,f2246])).

fof(f2246,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f2240])).

fof(f2878,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(superposition,[],[f2372,f2283])).

fof(f2283,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f2282])).

fof(f2372,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl11_4 ),
    inference(resolution,[],[f2227,f2255])).

fof(f2255,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f2254])).

fof(f2227,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f2172])).

fof(f2172,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2134])).

fof(f2134,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2088])).

fof(f2088,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f2868,plain,
    ( ~ spl11_9
    | spl11_2
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f2867,f2272,f2243,f2286])).

fof(f2243,plain,
    ( spl11_2
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f2272,plain,
    ( spl11_7
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f2867,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | spl11_2
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f2244,f2273])).

fof(f2273,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f2272])).

fof(f2244,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f2243])).

fof(f2862,plain,
    ( ~ spl11_9
    | spl11_1
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f2860,f2291,f2282,f2254,f2240,f2286])).

fof(f2860,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl11_4
    | ~ spl11_8
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f2849,f2292])).

fof(f2849,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl11_4
    | ~ spl11_8 ),
    inference(superposition,[],[f2370,f2283])).

fof(f2370,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl11_4 ),
    inference(resolution,[],[f2226,f2255])).

fof(f2226,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f2172])).

fof(f2733,plain,
    ( spl11_8
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f2723,f2272,f2265,f2282])).

fof(f2265,plain,
    ( spl11_6
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f2723,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(backward_demodulation,[],[f2266,f2273])).

fof(f2266,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f2265])).

fof(f2496,plain,
    ( spl11_7
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f2493,f2250,f2272])).

fof(f2250,plain,
    ( spl11_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f2493,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f2251,f2204])).

fof(f2204,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2125])).

fof(f2125,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2251,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f2250])).

fof(f2495,plain,
    ( spl11_6
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f2492,f2250,f2265])).

fof(f2492,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl11_3 ),
    inference(resolution,[],[f2251,f2203])).

fof(f2203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2124])).

fof(f2124,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2293,plain,
    ( spl11_10
    | ~ spl11_3
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f2289,f2272,f2250,f2291])).

fof(f2289,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_3
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f2280,f2251])).

fof(f2280,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_7 ),
    inference(superposition,[],[f2205,f2273])).

fof(f2205,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2288,plain,
    ( spl11_9
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f2279,f2272,f2243,f2286])).

fof(f2279,plain,
    ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl11_2
    | ~ spl11_7 ),
    inference(backward_demodulation,[],[f2247,f2273])).

fof(f2247,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f2243])).

fof(f2256,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f2178,f2254])).

fof(f2178,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2143,plain,
    ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2140,f2142,f2141])).

fof(f2141,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v3_pre_topc(X1,sK0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2142,plain,
    ( ? [X1] :
        ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v3_pre_topc(X1,sK0) )
        & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2140,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2139])).

fof(f2139,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v3_pre_topc(X1,X0) )
          & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2102])).

fof(f2102,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2090])).

fof(f2090,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f2089])).

fof(f2089,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f2252,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f2179,f2250])).

fof(f2179,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2248,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f2180,f2243,f2240])).

fof(f2180,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2245,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f2181,f2243,f2240])).

fof(f2181,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2143])).
%------------------------------------------------------------------------------
