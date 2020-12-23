%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1135+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 3.84s
% Output     : Refutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 227 expanded)
%              Number of leaves         :   25 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  350 ( 796 expanded)
%              Number of equality atoms :   68 ( 201 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2356,f2371,f2386,f2401,f2448,f2456,f2471,f2476,f2487,f2498,f2898,f2962,f3072,f6269])).

fof(f6269,plain,
    ( ~ spl46_1
    | ~ spl46_7
    | ~ spl46_18
    | ~ spl46_19
    | ~ spl46_23
    | ~ spl46_42
    | spl46_45
    | ~ spl46_53 ),
    inference(avatar_contradiction_clause,[],[f6268])).

fof(f6268,plain,
    ( $false
    | ~ spl46_1
    | ~ spl46_7
    | ~ spl46_18
    | ~ spl46_19
    | ~ spl46_23
    | ~ spl46_42
    | spl46_45
    | ~ spl46_53 ),
    inference(subsumption_resolution,[],[f6267,f2934])).

fof(f2934,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl46_1
    | ~ spl46_19
    | ~ spl46_42 ),
    inference(unit_resulting_resolution,[],[f2355,f2470,f2897,f2122])).

fof(f2122,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2012])).

fof(f2012,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1879])).

fof(f1879,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1857])).

fof(f1857,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f2897,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl46_42 ),
    inference(avatar_component_clause,[],[f2895])).

fof(f2895,plain,
    ( spl46_42
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_42])])).

fof(f2470,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl46_19 ),
    inference(avatar_component_clause,[],[f2468])).

fof(f2468,plain,
    ( spl46_19
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_19])])).

fof(f2355,plain,
    ( l1_pre_topc(sK0)
    | ~ spl46_1 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2353,plain,
    ( spl46_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_1])])).

fof(f6267,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl46_7
    | ~ spl46_18
    | ~ spl46_23
    | spl46_45
    | ~ spl46_53 ),
    inference(unit_resulting_resolution,[],[f3071,f2385,f2961,f2500])).

fof(f2500,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl46_18
    | ~ spl46_23 ),
    inference(subsumption_resolution,[],[f2499,f2455])).

fof(f2455,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl46_18 ),
    inference(avatar_component_clause,[],[f2453])).

fof(f2453,plain,
    ( spl46_18
  <=> v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_18])])).

fof(f2499,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
        | k1_pre_topc(sK0,sK1) = k1_pre_topc(X0,sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl46_23 ),
    inference(superposition,[],[f2309,f2497])).

fof(f2497,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl46_23 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f2495,plain,
    ( spl46_23
  <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_23])])).

fof(f2309,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2116])).

fof(f2116,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2011])).

fof(f2011,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1873])).

fof(f1873,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1872])).

fof(f1872,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1768])).

fof(f1768,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f2961,plain,
    ( k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl46_45 ),
    inference(avatar_component_clause,[],[f2959])).

fof(f2959,plain,
    ( spl46_45
  <=> k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_45])])).

fof(f2385,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl46_7 ),
    inference(avatar_component_clause,[],[f2383])).

fof(f2383,plain,
    ( spl46_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_7])])).

fof(f3071,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl46_53 ),
    inference(avatar_component_clause,[],[f3069])).

fof(f3069,plain,
    ( spl46_53
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_53])])).

fof(f3072,plain,
    ( spl46_53
    | ~ spl46_20 ),
    inference(avatar_split_clause,[],[f2792,f2473,f3069])).

fof(f2473,plain,
    ( spl46_20
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_20])])).

fof(f2792,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl46_20 ),
    inference(unit_resulting_resolution,[],[f2475,f2139])).

fof(f2139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1895])).

fof(f1895,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f2475,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl46_20 ),
    inference(avatar_component_clause,[],[f2473])).

fof(f2962,plain,
    ( ~ spl46_45
    | spl46_17
    | ~ spl46_18
    | ~ spl46_22
    | ~ spl46_42 ),
    inference(avatar_split_clause,[],[f2944,f2895,f2484,f2453,f2445,f2959])).

fof(f2445,plain,
    ( spl46_17
  <=> k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_17])])).

fof(f2484,plain,
    ( spl46_22
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_22])])).

fof(f2944,plain,
    ( k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl46_17
    | ~ spl46_18
    | ~ spl46_22
    | ~ spl46_42 ),
    inference(backward_demodulation,[],[f2447,f2943])).

fof(f2943,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl46_18
    | ~ spl46_22
    | ~ spl46_42 ),
    inference(forward_demodulation,[],[f2939,f2486])).

fof(f2486,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl46_22 ),
    inference(avatar_component_clause,[],[f2484])).

fof(f2939,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl46_18
    | ~ spl46_42 ),
    inference(unit_resulting_resolution,[],[f2455,f2897,f2152])).

fof(f2152,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f1906])).

fof(f1906,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1905])).

fof(f1905,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f2447,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | spl46_17 ),
    inference(avatar_component_clause,[],[f2445])).

fof(f2898,plain,
    ( spl46_42
    | ~ spl46_1
    | ~ spl46_19 ),
    inference(avatar_split_clause,[],[f2654,f2468,f2353,f2895])).

fof(f2654,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl46_1
    | ~ spl46_19 ),
    inference(unit_resulting_resolution,[],[f2470,f2355,f2135])).

fof(f2135,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f1894])).

fof(f1894,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2498,plain,
    ( spl46_23
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(avatar_split_clause,[],[f2449,f2368,f2353,f2495])).

fof(f2368,plain,
    ( spl46_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_4])])).

fof(f2449,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(unit_resulting_resolution,[],[f2355,f2370,f2349])).

fof(f2349,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f2348,f2106])).

fof(f2106,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1863])).

fof(f1863,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1862])).

fof(f1862,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1778])).

fof(f1778,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f2348,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f2310,f2107])).

fof(f2107,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1863])).

fof(f2310,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2115])).

fof(f2115,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2011])).

fof(f2370,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl46_4 ),
    inference(avatar_component_clause,[],[f2368])).

fof(f2487,plain,
    ( spl46_22
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(avatar_split_clause,[],[f2435,f2368,f2353,f2484])).

fof(f2435,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(unit_resulting_resolution,[],[f2355,f2370,f2117])).

fof(f2117,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f1874])).

fof(f1874,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1829])).

fof(f1829,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f2476,plain,
    ( spl46_20
    | ~ spl46_1 ),
    inference(avatar_split_clause,[],[f2417,f2353,f2473])).

fof(f2417,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl46_1 ),
    inference(unit_resulting_resolution,[],[f2355,f2127])).

fof(f2127,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1886])).

fof(f1886,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f2471,plain,
    ( spl46_19
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(avatar_split_clause,[],[f2427,f2368,f2353,f2468])).

fof(f2427,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(unit_resulting_resolution,[],[f2355,f2370,f2107])).

fof(f2456,plain,
    ( spl46_18
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(avatar_split_clause,[],[f2424,f2368,f2353,f2453])).

fof(f2424,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl46_1
    | ~ spl46_4 ),
    inference(unit_resulting_resolution,[],[f2355,f2370,f2106])).

fof(f2448,plain,
    ( ~ spl46_17
    | ~ spl46_1
    | ~ spl46_4
    | spl46_10 ),
    inference(avatar_split_clause,[],[f2438,f2398,f2368,f2353,f2445])).

fof(f2398,plain,
    ( spl46_10
  <=> g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl46_10])])).

fof(f2438,plain,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) != g1_pre_topc(sK1,u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl46_1
    | ~ spl46_4
    | spl46_10 ),
    inference(backward_demodulation,[],[f2400,f2435])).

fof(f2400,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl46_10 ),
    inference(avatar_component_clause,[],[f2398])).

fof(f2401,plain,(
    ~ spl46_10 ),
    inference(avatar_split_clause,[],[f2346,f2398])).

fof(f2346,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(backward_demodulation,[],[f2105,f2104])).

fof(f2104,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f2010])).

fof(f2010,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2)
    & sK1 = sK2
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1861,f2009,f2008,f2007])).

fof(f2007,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
                & X1 = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X1)),u1_pre_topc(k1_pre_topc(sK0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2008,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,X1)),u1_pre_topc(k1_pre_topc(sK0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
            & X1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
          & sK1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2009,plain,
    ( ? [X2] :
        ( k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) != g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
        & sK1 = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
   => ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2)
      & sK1 = sK2
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ) ),
    introduced(choice_axiom,[])).

fof(f1861,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1860])).

fof(f1860,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1859])).

fof(f1859,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
               => ( X1 = X2
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1858])).

fof(f1858,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).

fof(f2105,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2) ),
    inference(cnf_transformation,[],[f2010])).

fof(f2386,plain,(
    spl46_7 ),
    inference(avatar_split_clause,[],[f2347,f2383])).

fof(f2347,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(forward_demodulation,[],[f2103,f2104])).

fof(f2103,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f2010])).

fof(f2371,plain,(
    spl46_4 ),
    inference(avatar_split_clause,[],[f2102,f2368])).

fof(f2102,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2010])).

fof(f2356,plain,(
    spl46_1 ),
    inference(avatar_split_clause,[],[f2101,f2353])).

fof(f2101,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2010])).
%------------------------------------------------------------------------------
