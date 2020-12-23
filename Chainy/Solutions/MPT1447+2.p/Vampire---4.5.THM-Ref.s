%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1447+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 532 expanded)
%              Number of leaves         :   25 ( 205 expanded)
%              Depth                    :   16
%              Number of atoms          : 1097 (2885 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2862,f2865,f2867,f2871,f2875,f2879,f2883,f2887,f2891,f2930,f2958,f2966,f2970,f2978,f3001,f3012,f3031,f3039,f3044,f3047,f3066,f3071,f3074,f3100,f3102,f3120])).

fof(f3120,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f3119])).

fof(f3119,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3118,f2890])).

fof(f2890,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f2889])).

fof(f2889,plain,
    ( spl4_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f3118,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3117,f2886])).

fof(f2886,plain,
    ( v10_lattices(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f2885])).

fof(f2885,plain,
    ( spl4_8
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f3117,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3116,f2882])).

fof(f2882,plain,
    ( l3_lattices(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f2881])).

fof(f2881,plain,
    ( spl4_7
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f3116,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3115,f2878])).

fof(f2878,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f2877])).

fof(f2877,plain,
    ( spl4_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f3115,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3114,f2874])).

fof(f2874,plain,
    ( v10_lattices(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f2873])).

fof(f2873,plain,
    ( spl4_5
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f3114,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3113,f2870])).

fof(f2870,plain,
    ( l3_lattices(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f2869])).

fof(f2869,plain,
    ( spl4_4
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3113,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_21
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3112,f3030])).

fof(f3030,plain,
    ( v14_lattices(sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f2956])).

fof(f2956,plain,
    ( spl4_21
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f3112,plain,
    ( ~ v14_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f3110,f3065])).

fof(f3065,plain,
    ( v14_lattices(sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f3037])).

fof(f3037,plain,
    ( spl4_24
  <=> v14_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f3110,plain,
    ( ~ v14_lattices(sK1)
    | ~ v14_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_22 ),
    inference(resolution,[],[f3101,f2815])).

fof(f2815,plain,(
    ! [X0,X1] :
      ( v14_lattices(k7_filter_1(X0,X1))
      | ~ v14_lattices(X1)
      | ~ v14_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f2791,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v14_lattices(X1)
                & v14_lattices(X0) )
              | ~ v14_lattices(k7_filter_1(X0,X1)) )
            & ( v14_lattices(k7_filter_1(X0,X1))
              | ~ v14_lattices(X1)
              | ~ v14_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2790])).

fof(f2790,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v14_lattices(X1)
                & v14_lattices(X0) )
              | ~ v14_lattices(k7_filter_1(X0,X1)) )
            & ( v14_lattices(k7_filter_1(X0,X1))
              | ~ v14_lattices(X1)
              | ~ v14_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2772])).

fof(f2772,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2771])).

fof(f2771,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2732])).

fof(f2732,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v14_lattices(X1)
              & v14_lattices(X0) )
          <=> v14_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_filter_1)).

fof(f3101,plain,
    ( ~ v14_lattices(k7_filter_1(sK0,sK1))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f2968])).

fof(f2968,plain,
    ( spl4_22
  <=> v14_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f3102,plain,
    ( spl4_15
    | ~ spl4_16
    | ~ spl4_17
    | ~ spl4_22
    | spl4_3 ),
    inference(avatar_split_clause,[],[f3075,f2860,f2968,f2928,f2925,f2922])).

fof(f2922,plain,
    ( spl4_15
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f2925,plain,
    ( spl4_16
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f2928,plain,
    ( spl4_17
  <=> v13_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f2860,plain,
    ( spl4_3
  <=> v15_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f3075,plain,
    ( ~ v14_lattices(k7_filter_1(sK0,sK1))
    | ~ v13_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | spl4_3 ),
    inference(resolution,[],[f2861,f2842])).

fof(f2842,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2797])).

fof(f2797,plain,(
    ! [X0] :
      ( ( ( v15_lattices(X0)
          | ~ v14_lattices(X0)
          | ~ v13_lattices(X0) )
        & ( ( v14_lattices(X0)
            & v13_lattices(X0) )
          | ~ v15_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2796])).

fof(f2796,plain,(
    ! [X0] :
      ( ( ( v15_lattices(X0)
          | ~ v14_lattices(X0)
          | ~ v13_lattices(X0) )
        & ( ( v14_lattices(X0)
            & v13_lattices(X0) )
          | ~ v15_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2778])).

fof(f2778,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
      <=> ( v14_lattices(X0)
          & v13_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2777])).

% (32621)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
fof(f2777,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
      <=> ( v14_lattices(X0)
          & v13_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2591])).

fof(f2591,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v15_lattices(X0)
      <=> ( v14_lattices(X0)
          & v13_lattices(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_lattices)).

fof(f2861,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f2860])).

fof(f3100,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f3099])).

fof(f3099,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3098,f2890])).

fof(f3098,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3097,f2886])).

fof(f3097,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3096,f2882])).

fof(f3096,plain,
    ( ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3095,f2878])).

fof(f3095,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3094,f2874])).

fof(f3094,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3093,f2870])).

fof(f3093,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_17
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3092,f3000])).

fof(f3000,plain,
    ( v13_lattices(sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f2953])).

fof(f2953,plain,
    ( spl4_20
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f3092,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_17
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3090,f3011])).

fof(f3011,plain,
    ( v13_lattices(sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f3010])).

fof(f3010,plain,
    ( spl4_23
  <=> v13_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f3090,plain,
    ( ~ v13_lattices(sK1)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_17 ),
    inference(resolution,[],[f3079,f2812])).

fof(f2812,plain,(
    ! [X0,X1] :
      ( v13_lattices(k7_filter_1(X0,X1))
      | ~ v13_lattices(X1)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2789])).

fof(f2789,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v13_lattices(X1)
                & v13_lattices(X0) )
              | ~ v13_lattices(k7_filter_1(X0,X1)) )
            & ( v13_lattices(k7_filter_1(X0,X1))
              | ~ v13_lattices(X1)
              | ~ v13_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2788])).

fof(f2788,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v13_lattices(X1)
                & v13_lattices(X0) )
              | ~ v13_lattices(k7_filter_1(X0,X1)) )
            & ( v13_lattices(k7_filter_1(X0,X1))
              | ~ v13_lattices(X1)
              | ~ v13_lattices(X0) ) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2770])).

fof(f2770,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2769])).

fof(f2769,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) )
          | ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2730])).

fof(f2730,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v13_lattices(X1)
              & v13_lattices(X0) )
          <=> v13_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_filter_1)).

fof(f3079,plain,
    ( ~ v13_lattices(k7_filter_1(sK0,sK1))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f2928])).

fof(f3074,plain,
    ( spl4_23
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f3073,f2877,f2869,f2857,f3010])).

fof(f2857,plain,
    ( spl4_2
  <=> v15_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f3073,plain,
    ( v13_lattices(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f3072,f2878])).

fof(f3072,plain,
    ( v13_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f3068,f2870])).

fof(f3068,plain,
    ( v13_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f2863,f2840])).

fof(f2840,plain,(
    ! [X0] :
      ( ~ v15_lattices(X0)
      | v13_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2797])).

fof(f2863,plain,
    ( v15_lattices(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f2857])).

fof(f3071,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f3070,f2877,f2869,f2857,f3037])).

fof(f3070,plain,
    ( v14_lattices(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f3069,f2878])).

fof(f3069,plain,
    ( v14_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f3067,f2870])).

fof(f3067,plain,
    ( v14_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f2863,f2841])).

fof(f2841,plain,(
    ! [X0] :
      ( ~ v15_lattices(X0)
      | v14_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2797])).

fof(f3066,plain,
    ( spl4_24
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f3064,f2968,f2889,f2885,f2881,f2877,f2873,f2869,f3037])).

fof(f3064,plain,
    ( v14_lattices(sK1)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3063,f2890])).

fof(f3063,plain,
    ( v14_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3062,f2886])).

fof(f3062,plain,
    ( v14_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3061,f2882])).

fof(f3061,plain,
    ( v14_lattices(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3060,f2878])).

fof(f3060,plain,
    ( v14_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3059,f2874])).

fof(f3059,plain,
    ( v14_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3049,f2870])).

fof(f3049,plain,
    ( v14_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_22 ),
    inference(resolution,[],[f2817,f2969])).

fof(f2969,plain,
    ( v14_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f2968])).

fof(f2817,plain,(
    ! [X0,X1] :
      ( ~ v14_lattices(k7_filter_1(X0,X1))
      | v14_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f3047,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(avatar_split_clause,[],[f3046,f2889,f2881,f2854,f2953])).

fof(f2854,plain,
    ( spl4_1
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f3046,plain,
    ( v13_lattices(sK0)
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(subsumption_resolution,[],[f3045,f2890])).

fof(f3045,plain,
    ( v13_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f3041,f2882])).

fof(f3041,plain,
    ( v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f2866,f2840])).

fof(f2866,plain,
    ( v15_lattices(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f2854])).

fof(f3044,plain,
    ( spl4_21
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(avatar_split_clause,[],[f3043,f2889,f2881,f2854,f2956])).

fof(f3043,plain,
    ( v14_lattices(sK0)
    | ~ spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(subsumption_resolution,[],[f3042,f2890])).

fof(f3042,plain,
    ( v14_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f3040,f2882])).

fof(f3040,plain,
    ( v14_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f2866,f2841])).

fof(f3039,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f3034,f2877,f2869,f2857,f3037,f3010])).

fof(f3034,plain,
    ( ~ v14_lattices(sK1)
    | ~ v13_lattices(sK1)
    | spl4_2
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f3033,f2878])).

fof(f3033,plain,
    ( ~ v14_lattices(sK1)
    | ~ v13_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f3032,f2870])).

fof(f3032,plain,
    ( ~ v14_lattices(sK1)
    | ~ v13_lattices(sK1)
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | spl4_2 ),
    inference(resolution,[],[f2858,f2842])).

fof(f2858,plain,
    ( ~ v15_lattices(sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f2857])).

fof(f3031,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f3029,f2968,f2889,f2885,f2881,f2877,f2873,f2869,f2956])).

fof(f3029,plain,
    ( v14_lattices(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3028,f2890])).

fof(f3028,plain,
    ( v14_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3027,f2886])).

fof(f3027,plain,
    ( v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3026,f2882])).

fof(f3026,plain,
    ( v14_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3025,f2878])).

fof(f3025,plain,
    ( v14_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3024,f2874])).

fof(f3024,plain,
    ( v14_lattices(sK0)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f3014,f2870])).

fof(f3014,plain,
    ( v14_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_22 ),
    inference(resolution,[],[f2816,f2969])).

fof(f2816,plain,(
    ! [X0,X1] :
      ( ~ v14_lattices(k7_filter_1(X0,X1))
      | v14_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2791])).

fof(f3012,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f3008,f2928,f2889,f2885,f2881,f2877,f2873,f2869,f3010])).

fof(f3008,plain,
    ( v13_lattices(sK1)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f3007,f2890])).

fof(f3007,plain,
    ( v13_lattices(sK1)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f3006,f2886])).

fof(f3006,plain,
    ( v13_lattices(sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f3005,f2882])).

fof(f3005,plain,
    ( v13_lattices(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f3004,f2878])).

fof(f3004,plain,
    ( v13_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f3003,f2874])).

fof(f3003,plain,
    ( v13_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f3002,f2870])).

fof(f3002,plain,
    ( v13_lattices(sK1)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f2814,f2929])).

fof(f2929,plain,
    ( v13_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f2928])).

fof(f2814,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(k7_filter_1(X0,X1))
      | v13_lattices(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2789])).

fof(f3001,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f2999,f2928,f2889,f2885,f2881,f2877,f2873,f2869,f2953])).

fof(f2999,plain,
    ( v13_lattices(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | spl4_9
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f2998,f2890])).

fof(f2998,plain,
    ( v13_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f2997,f2886])).

fof(f2997,plain,
    ( v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f2996,f2882])).

fof(f2996,plain,
    ( v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f2995,f2878])).

fof(f2995,plain,
    ( v13_lattices(sK0)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f2994,f2874])).

fof(f2994,plain,
    ( v13_lattices(sK0)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f2984,f2870])).

fof(f2984,plain,
    ( v13_lattices(sK0)
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_17 ),
    inference(resolution,[],[f2813,f2929])).

fof(f2813,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(k7_filter_1(X0,X1))
      | v13_lattices(X0)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2789])).

fof(f2978,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | spl4_9
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f2977])).

fof(f2977,plain,
    ( $false
    | ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | spl4_9
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f2976,f2890])).

fof(f2976,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f2975,f2882])).

fof(f2975,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f2974,f2878])).

fof(f2974,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f2972,f2870])).

fof(f2972,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f2811,f2923])).

fof(f2923,plain,
    ( v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f2922])).

fof(f2811,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2768])).

fof(f2768,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2767])).

fof(f2767,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2750])).

fof(f2750,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ~ v2_struct_0(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2637])).

fof(f2637,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattices(k7_filter_1(X0,X1))
        & ~ v2_struct_0(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_filter_1)).

fof(f2970,plain,
    ( spl4_15
    | ~ spl4_16
    | spl4_22
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f2937,f2860,f2968,f2925,f2922])).

fof(f2937,plain,
    ( v14_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f2841,f2864])).

fof(f2864,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f2860])).

fof(f2966,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | spl4_9
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f2965])).

fof(f2965,plain,
    ( $false
    | ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | spl4_9
    | spl4_16 ),
    inference(subsumption_resolution,[],[f2964,f2890])).

fof(f2964,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_6
    | ~ spl4_7
    | spl4_16 ),
    inference(subsumption_resolution,[],[f2963,f2882])).

fof(f2963,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_6
    | spl4_16 ),
    inference(subsumption_resolution,[],[f2962,f2878])).

fof(f2962,plain,
    ( v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_16 ),
    inference(subsumption_resolution,[],[f2960,f2870])).

fof(f2960,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_16 ),
    inference(resolution,[],[f2810,f2926])).

fof(f2926,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f2925])).

fof(f2810,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2766])).

fof(f2766,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2765])).

fof(f2765,plain,(
    ! [X0,X1] :
      ( l3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2752])).

fof(f2752,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => l3_lattices(k7_filter_1(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2622])).

fof(f2622,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(f2958,plain,
    ( ~ spl4_20
    | ~ spl4_21
    | spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(avatar_split_clause,[],[f2951,f2889,f2881,f2854,f2956,f2953])).

fof(f2951,plain,
    ( ~ v14_lattices(sK0)
    | ~ v13_lattices(sK0)
    | spl4_1
    | ~ spl4_7
    | spl4_9 ),
    inference(subsumption_resolution,[],[f2950,f2890])).

fof(f2950,plain,
    ( ~ v14_lattices(sK0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f2945,f2882])).

fof(f2945,plain,
    ( ~ v14_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_1 ),
    inference(resolution,[],[f2842,f2855])).

fof(f2855,plain,
    ( ~ v15_lattices(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f2854])).

fof(f2930,plain,
    ( spl4_15
    | ~ spl4_16
    | spl4_17
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f2919,f2860,f2928,f2925,f2922])).

fof(f2919,plain,
    ( v13_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f2840,f2864])).

fof(f2891,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f2800,f2889])).

fof(f2800,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2787,plain,
    ( ( ~ v15_lattices(k7_filter_1(sK0,sK1))
      | ~ v15_lattices(sK1)
      | ~ v15_lattices(sK0) )
    & ( v15_lattices(k7_filter_1(sK0,sK1))
      | ( v15_lattices(sK1)
        & v15_lattices(sK0) ) )
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2784,f2786,f2785])).

fof(f2785,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v15_lattices(k7_filter_1(X0,X1))
              | ~ v15_lattices(X1)
              | ~ v15_lattices(X0) )
            & ( v15_lattices(k7_filter_1(X0,X1))
              | ( v15_lattices(X1)
                & v15_lattices(X0) ) )
            & l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(sK0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(sK0) )
          & ( v15_lattices(k7_filter_1(sK0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(sK0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2786,plain,
    ( ? [X1] :
        ( ( ~ v15_lattices(k7_filter_1(sK0,X1))
          | ~ v15_lattices(X1)
          | ~ v15_lattices(sK0) )
        & ( v15_lattices(k7_filter_1(sK0,X1))
          | ( v15_lattices(X1)
            & v15_lattices(sK0) ) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ v15_lattices(k7_filter_1(sK0,sK1))
        | ~ v15_lattices(sK1)
        | ~ v15_lattices(sK0) )
      & ( v15_lattices(k7_filter_1(sK0,sK1))
        | ( v15_lattices(sK1)
          & v15_lattices(sK0) ) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2784,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(X0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(X0) )
          & ( v15_lattices(k7_filter_1(X0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2783])).

fof(f2783,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v15_lattices(k7_filter_1(X0,X1))
            | ~ v15_lattices(X1)
            | ~ v15_lattices(X0) )
          & ( v15_lattices(k7_filter_1(X0,X1))
            | ( v15_lattices(X1)
              & v15_lattices(X0) ) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2762])).

fof(f2762,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <~> v15_lattices(k7_filter_1(X0,X1)) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2761])).

fof(f2761,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <~> v15_lattices(k7_filter_1(X0,X1)) )
          & l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2735])).

fof(f2735,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( v15_lattices(X1)
                & v15_lattices(X0) )
            <=> v15_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f2734])).

fof(f2734,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & v10_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( v15_lattices(X1)
              & v15_lattices(X0) )
          <=> v15_lattices(k7_filter_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_filter_1)).

fof(f2887,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f2801,f2885])).

fof(f2801,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2883,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f2802,f2881])).

fof(f2802,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2879,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f2803,f2877])).

fof(f2803,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2875,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f2804,f2873])).

fof(f2804,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2871,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f2805,f2869])).

fof(f2805,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2867,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f2806,f2860,f2854])).

fof(f2806,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK0) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2865,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f2807,f2860,f2857])).

fof(f2807,plain,
    ( v15_lattices(k7_filter_1(sK0,sK1))
    | v15_lattices(sK1) ),
    inference(cnf_transformation,[],[f2787])).

fof(f2862,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f2808,f2860,f2857,f2854])).

fof(f2808,plain,
    ( ~ v15_lattices(k7_filter_1(sK0,sK1))
    | ~ v15_lattices(sK1)
    | ~ v15_lattices(sK0) ),
    inference(cnf_transformation,[],[f2787])).
%------------------------------------------------------------------------------
