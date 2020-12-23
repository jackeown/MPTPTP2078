%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1299+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:17 EST 2020

% Result     : Theorem 0.95s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   49 (  98 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 372 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2464,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2349,f2352,f2356,f2360,f2371,f2448,f2462,f2463])).

% (5448)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
fof(f2463,plain,
    ( ~ spl7_2
    | ~ spl7_18
    | spl7_1
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f2435,f2369,f2358,f2344,f2438,f2347])).

fof(f2347,plain,
    ( spl7_2
  <=> v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f2438,plain,
    ( spl7_18
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f2344,plain,
    ( spl7_1
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

% (5445)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f2358,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f2369,plain,
    ( spl7_6
  <=> sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f2435,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(superposition,[],[f2415,f2370])).

fof(f2370,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f2369])).

% (5447)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
fof(f2415,plain,
    ( ! [X0] :
        ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v2_tops_2(X0,sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f2313,f2359])).

fof(f2359,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f2358])).

fof(f2313,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f2289])).

fof(f2289,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2262])).

fof(f2262,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2250])).

fof(f2250,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(f2462,plain,
    ( spl7_2
    | ~ spl7_18
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f2457,f2369,f2358,f2344,f2438,f2347])).

fof(f2457,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(superposition,[],[f2433,f2370])).

fof(f2433,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X0,sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f2314,f2359])).

fof(f2314,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2289])).

fof(f2448,plain,
    ( ~ spl7_3
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f2447])).

fof(f2447,plain,
    ( $false
    | ~ spl7_3
    | spl7_18 ),
    inference(subsumption_resolution,[],[f2445,f2355])).

fof(f2355,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f2354,plain,
    ( spl7_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f2445,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_18 ),
    inference(resolution,[],[f2439,f2331])).

fof(f2331,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2276])).

fof(f2276,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f565])).

fof(f565,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f2439,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f2438])).

fof(f2371,plain,
    ( spl7_6
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f2365,f2354,f2369])).

fof(f2365,plain,
    ( sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ spl7_3 ),
    inference(resolution,[],[f2332,f2355])).

fof(f2332,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2277])).

fof(f2277,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f574])).

fof(f574,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f2360,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f2305,f2358])).

fof(f2305,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2284])).

fof(f2284,plain,
    ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v1_tops_2(sK1,sK0) )
    & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2281,f2283,f2282])).

fof(f2282,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v1_tops_2(X1,X0) )
            & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | ~ v1_tops_2(X1,sK0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2283,plain,
    ( ? [X1] :
        ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | ~ v1_tops_2(X1,sK0) )
        & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | v1_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v1_tops_2(sK1,sK0) )
      & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | v1_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f2281,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2280])).

fof(f2280,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2259])).

fof(f2259,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2252])).

fof(f2252,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f2251])).

fof(f2251,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

fof(f2356,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f2306,f2354])).

fof(f2306,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f2284])).

fof(f2352,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f2307,f2347,f2344])).

fof(f2307,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f2284])).

fof(f2349,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f2308,f2347,f2344])).

fof(f2308,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f2284])).
%------------------------------------------------------------------------------
