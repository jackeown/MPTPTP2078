%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1228+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 121 expanded)
%              Number of leaves         :   15 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  188 ( 624 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2505,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2238,f2242,f2246,f2250,f2254,f2258,f2262,f2383,f2409,f2503])).

fof(f2503,plain,
    ( ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_7
    | spl12_24 ),
    inference(avatar_contradiction_clause,[],[f2501])).

fof(f2501,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5
    | ~ spl12_6
    | ~ spl12_7
    | spl12_24 ),
    inference(unit_resulting_resolution,[],[f2261,f2257,f2241,f2245,f2408,f2253,f2249,f2190])).

fof(f2190,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2121,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2120])).

fof(f2120,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2089])).

fof(f2089,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f2249,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f2248])).

fof(f2248,plain,
    ( spl12_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f2253,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f2252])).

fof(f2252,plain,
    ( spl12_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f2408,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | spl12_24 ),
    inference(avatar_component_clause,[],[f2407])).

fof(f2407,plain,
    ( spl12_24
  <=> v3_pre_topc(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f2245,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f2244])).

fof(f2244,plain,
    ( spl12_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f2241,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f2240])).

fof(f2240,plain,
    ( spl12_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f2257,plain,
    ( l1_pre_topc(sK0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f2256])).

fof(f2256,plain,
    ( spl12_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f2261,plain,
    ( v2_pre_topc(sK0)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f2260])).

fof(f2260,plain,
    ( spl12_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f2409,plain,
    ( ~ spl12_24
    | spl12_1
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f2404,f2381,f2236,f2407])).

fof(f2236,plain,
    ( spl12_1
  <=> v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f2381,plain,
    ( spl12_20
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f2404,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK1,sK2),sK0)
    | spl12_1
    | ~ spl12_20 ),
    inference(backward_demodulation,[],[f2237,f2382])).

fof(f2382,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f2381])).

fof(f2237,plain,
    ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f2236])).

fof(f2383,plain,
    ( spl12_20
    | ~ spl12_4
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f2370,f2252,f2248,f2381])).

fof(f2370,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl12_4
    | ~ spl12_5 ),
    inference(resolution,[],[f2338,f2253])).

fof(f2338,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(X0,sK2) = k4_subset_1(u1_struct_0(sK0),X0,sK2) )
    | ~ spl12_4 ),
    inference(resolution,[],[f2181,f2249])).

fof(f2181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2109])).

fof(f2109,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2108])).

fof(f2108,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f2262,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f2173,f2260])).

fof(f2173,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2142])).

fof(f2142,plain,
    ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2105,f2141,f2140,f2139])).

fof(f2139,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2140,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v3_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v3_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2141,plain,
    ( ? [X2] :
        ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v3_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2105,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2104])).

fof(f2104,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2101])).

fof(f2101,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f2100])).

fof(f2100,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tops_1)).

fof(f2258,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f2174,f2256])).

fof(f2174,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2142])).

fof(f2254,plain,(
    spl12_5 ),
    inference(avatar_split_clause,[],[f2175,f2252])).

fof(f2175,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2142])).

fof(f2250,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f2176,f2248])).

fof(f2176,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2142])).

fof(f2246,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f2177,f2244])).

fof(f2177,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2142])).

fof(f2242,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f2178,f2240])).

fof(f2178,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2142])).

fof(f2238,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f2179,f2236])).

fof(f2179,plain,(
    ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f2142])).
%------------------------------------------------------------------------------
