%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1294+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  86 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  144 ( 248 expanded)
%              Number of equality atoms :   60 ( 127 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2524,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2347,f2353,f2357,f2448,f2449,f2497,f2513,f2523])).

fof(f2523,plain,(
    spl6_18 ),
    inference(avatar_contradiction_clause,[],[f2522])).

fof(f2522,plain,
    ( $false
    | spl6_18 ),
    inference(subsumption_resolution,[],[f2520,f2333])).

fof(f2333,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2520,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl6_18 ),
    inference(resolution,[],[f2512,f2313])).

fof(f2313,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2262])).

fof(f2262,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f565])).

fof(f565,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f2512,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f2511])).

fof(f2511,plain,
    ( spl6_18
  <=> m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f2513,plain,
    ( ~ spl6_18
    | spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f2509,f2495,f2351,f2511])).

fof(f2351,plain,
    ( spl6_3
  <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2495,plain,
    ( spl6_17
  <=> k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f2509,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl6_3
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f2508,f2352])).

fof(f2352,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f2351])).

fof(f2508,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_17 ),
    inference(trivial_inequality_removal,[],[f2506])).

fof(f2506,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_17 ),
    inference(superposition,[],[f2311,f2496])).

fof(f2496,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f2311,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2259])).

fof(f2259,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f2258])).

fof(f2258,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f613])).

fof(f613,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f2497,plain,
    ( spl6_17
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f2493,f2419,f2345,f2495])).

fof(f2345,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f2419,plain,
    ( spl6_12
  <=> sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2493,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f2420,f2346])).

fof(f2346,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f2345])).

fof(f2420,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f2419])).

fof(f2449,plain,
    ( spl6_12
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f2430,f2355,f2419])).

fof(f2355,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2430,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl6_4 ),
    inference(resolution,[],[f2356,f2314])).

fof(f2314,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2263])).

fof(f2263,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f574])).

fof(f574,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f2356,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f2355])).

fof(f2448,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f2447])).

fof(f2447,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f2446,f2356])).

fof(f2446,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f2444,f2349])).

fof(f2349,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f2345])).

fof(f2444,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f2442])).

fof(f2442,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl6_1 ),
    inference(superposition,[],[f2311,f2343])).

fof(f2343,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f2342])).

fof(f2342,plain,
    ( spl6_1
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2357,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f2294,f2355])).

fof(f2294,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f2278])).

fof(f2278,plain,
    ( ( ( k1_xboole_0 = sK1
        & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
      | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2249,f2277])).

fof(f2277,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
          | ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ( k1_xboole_0 = sK1
          & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
        | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2249,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2244])).

fof(f2244,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f2243])).

fof(f2243,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

fof(f2353,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f2348,f2351,f2345])).

fof(f2348,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f2295])).

fof(f2295,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f2278])).

fof(f2347,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f2298,f2345,f2342])).

fof(f2298,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f2278])).
%------------------------------------------------------------------------------
