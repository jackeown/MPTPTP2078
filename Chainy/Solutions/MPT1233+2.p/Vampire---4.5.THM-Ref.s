%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1233+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:13 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 241 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  265 ( 540 expanded)
%              Number of equality atoms :   62 ( 138 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3866,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3088,f3093,f3103,f3128,f3185,f3218,f3358,f3767,f3849])).

fof(f3849,plain,
    ( ~ spl68_2
    | ~ spl68_15
    | spl68_16
    | ~ spl68_25
    | ~ spl68_30 ),
    inference(avatar_contradiction_clause,[],[f3848])).

fof(f3848,plain,
    ( $false
    | ~ spl68_2
    | ~ spl68_15
    | spl68_16
    | ~ spl68_25
    | ~ spl68_30 ),
    inference(subsumption_resolution,[],[f3847,f3217])).

fof(f3217,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl68_16 ),
    inference(avatar_component_clause,[],[f3215])).

fof(f3215,plain,
    ( spl68_16
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_16])])).

fof(f3847,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl68_2
    | ~ spl68_15
    | ~ spl68_25
    | ~ spl68_30 ),
    inference(forward_demodulation,[],[f3844,f3665])).

fof(f3665,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f3659,f2892])).

fof(f2892,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f3659,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f2743,f2618])).

fof(f2618,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2175])).

fof(f2175,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2743,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3844,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl68_2
    | ~ spl68_15
    | ~ spl68_25
    | ~ spl68_30 ),
    inference(backward_demodulation,[],[f3703,f3805])).

fof(f3805,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl68_2
    | ~ spl68_30 ),
    inference(unit_resulting_resolution,[],[f3092,f2743,f3766,f2592])).

fof(f2592,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2150])).

fof(f2150,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2149])).

fof(f2149,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f3766,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl68_30 ),
    inference(avatar_component_clause,[],[f3764])).

fof(f3764,plain,
    ( spl68_30
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_30])])).

fof(f3092,plain,
    ( l1_pre_topc(sK0)
    | ~ spl68_2 ),
    inference(avatar_component_clause,[],[f3090])).

fof(f3090,plain,
    ( spl68_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_2])])).

fof(f3703,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl68_2
    | ~ spl68_15
    | ~ spl68_25 ),
    inference(backward_demodulation,[],[f3672,f3684])).

fof(f3684,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl68_2
    | ~ spl68_15 ),
    inference(backward_demodulation,[],[f3670,f3682])).

fof(f3682,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f3658,f3665])).

fof(f3658,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f2743,f2617])).

fof(f2617,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2174])).

fof(f2174,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f3670,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl68_2
    | ~ spl68_15 ),
    inference(forward_demodulation,[],[f3667,f3264])).

fof(f3264,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl68_2
    | ~ spl68_15 ),
    inference(forward_demodulation,[],[f3262,f3210])).

fof(f3210,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl68_15 ),
    inference(unit_resulting_resolution,[],[f3184,f2576])).

fof(f2576,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2132])).

fof(f2132,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3184,plain,
    ( l1_struct_0(sK0)
    | ~ spl68_15 ),
    inference(avatar_component_clause,[],[f3182])).

fof(f3182,plain,
    ( spl68_15
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_15])])).

fof(f3262,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ spl68_2 ),
    inference(unit_resulting_resolution,[],[f3092,f2595])).

fof(f2595,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f2152])).

fof(f2152,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2098])).

fof(f2098,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f3667,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl68_2 ),
    inference(backward_demodulation,[],[f3201,f3665])).

fof(f3201,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl68_2 ),
    inference(backward_demodulation,[],[f3175,f3186])).

fof(f3186,plain,(
    ! [X0] : k1_xboole_0 = sK10(X0) ),
    inference(unit_resulting_resolution,[],[f2639,f2643])).

fof(f2643,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2192])).

fof(f2192,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2639,plain,(
    ! [X0] : v1_xboole_0(sK10(X0)) ),
    inference(cnf_transformation,[],[f2450])).

fof(f2450,plain,(
    ! [X0] :
      ( v1_xboole_0(sK10(X0))
      & m1_subset_1(sK10(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f490,f2449])).

fof(f2449,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK10(X0))
        & m1_subset_1(sK10(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f490,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f3175,plain,
    ( k1_tops_1(sK0,sK10(u1_struct_0(sK0))) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK10(u1_struct_0(sK0)))))
    | ~ spl68_2 ),
    inference(unit_resulting_resolution,[],[f3092,f2638,f2571])).

fof(f2571,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f2124])).

fof(f2124,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2086])).

fof(f2086,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f2638,plain,(
    ! [X0] : m1_subset_1(sK10(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2450])).

fof(f3672,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_xboole_0)))
    | ~ spl68_2
    | ~ spl68_15
    | ~ spl68_25 ),
    inference(backward_demodulation,[],[f3425,f3671])).

fof(f3671,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl68_2
    | ~ spl68_15
    | ~ spl68_25 ),
    inference(backward_demodulation,[],[f3401,f3670])).

fof(f3401,plain,
    ( k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl68_25 ),
    inference(unit_resulting_resolution,[],[f3357,f2618])).

fof(f3357,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl68_25 ),
    inference(avatar_component_clause,[],[f3355])).

fof(f3355,plain,
    ( spl68_25
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_25])])).

fof(f3425,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl68_2
    | ~ spl68_25 ),
    inference(forward_demodulation,[],[f3368,f3401])).

fof(f3368,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl68_2
    | ~ spl68_25 ),
    inference(unit_resulting_resolution,[],[f3092,f3357,f2571])).

fof(f3767,plain,
    ( spl68_30
    | ~ spl68_1
    | ~ spl68_2
    | ~ spl68_9 ),
    inference(avatar_split_clause,[],[f3597,f3125,f3090,f3085,f3764])).

fof(f3085,plain,
    ( spl68_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_1])])).

fof(f3125,plain,
    ( spl68_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_9])])).

fof(f3597,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl68_1
    | ~ spl68_2
    | ~ spl68_9 ),
    inference(unit_resulting_resolution,[],[f3087,f3092,f3127,f2743,f2672])).

fof(f2672,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f2219])).

fof(f2219,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2218])).

fof(f2218,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1762])).

fof(f1762,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f3127,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl68_9 ),
    inference(avatar_component_clause,[],[f3125])).

fof(f3087,plain,
    ( v2_pre_topc(sK0)
    | ~ spl68_1 ),
    inference(avatar_component_clause,[],[f3085])).

fof(f3358,plain,
    ( spl68_25
    | ~ spl68_15 ),
    inference(avatar_split_clause,[],[f3213,f3182,f3355])).

fof(f3213,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl68_15 ),
    inference(forward_demodulation,[],[f3209,f3210])).

fof(f3209,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl68_15 ),
    inference(unit_resulting_resolution,[],[f3184,f2575])).

fof(f2575,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2131])).

fof(f2131,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1781])).

fof(f1781,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f3218,plain,
    ( ~ spl68_16
    | spl68_4
    | ~ spl68_15 ),
    inference(avatar_split_clause,[],[f3212,f3182,f3100,f3215])).

fof(f3100,plain,
    ( spl68_4
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl68_4])])).

fof(f3212,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl68_4
    | ~ spl68_15 ),
    inference(backward_demodulation,[],[f3102,f3210])).

fof(f3102,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    | spl68_4 ),
    inference(avatar_component_clause,[],[f3100])).

fof(f3185,plain,
    ( spl68_15
    | ~ spl68_2 ),
    inference(avatar_split_clause,[],[f3170,f3090,f3182])).

fof(f3170,plain,
    ( l1_struct_0(sK0)
    | ~ spl68_2 ),
    inference(unit_resulting_resolution,[],[f3092,f2659])).

fof(f2659,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2206])).

fof(f2206,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f3128,plain,(
    spl68_9 ),
    inference(avatar_split_clause,[],[f2652,f3125])).

fof(f2652,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f3103,plain,(
    ~ spl68_4 ),
    inference(avatar_split_clause,[],[f2568,f3100])).

fof(f2568,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2418])).

fof(f2418,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2119,f2417])).

fof(f2417,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2119,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2118])).

fof(f2118,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2112])).

fof(f2112,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f2111])).

fof(f2111,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f3093,plain,(
    spl68_2 ),
    inference(avatar_split_clause,[],[f2567,f3090])).

fof(f2567,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2418])).

fof(f3088,plain,(
    spl68_1 ),
    inference(avatar_split_clause,[],[f2566,f3085])).

fof(f2566,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2418])).
%------------------------------------------------------------------------------
