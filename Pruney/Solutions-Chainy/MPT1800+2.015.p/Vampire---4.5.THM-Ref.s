%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 485 expanded)
%              Number of leaves         :   48 ( 215 expanded)
%              Depth                    :   10
%              Number of atoms          : 1127 (2062 expanded)
%              Number of equality atoms :  145 ( 249 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f66,f70,f74,f78,f85,f93,f97,f101,f105,f109,f117,f121,f131,f139,f148,f157,f165,f170,f178,f191,f195,f203,f207,f211,f234,f238,f265,f278,f309,f319,f320,f339,f360,f364,f383,f402,f419,f436,f457])).

fof(f457,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_41
    | ~ spl3_61 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_41
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f81,f438])).

fof(f438,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f56,f437])).

fof(f437,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f282,f418])).

fof(f418,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl3_61
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f282,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_tsep_1(sK1,sK0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f281,f69])).

fof(f69,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f281,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f280,f65])).

fof(f65,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f280,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f279,f73])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f279,plain,
    ( ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_41 ),
    inference(resolution,[],[f277,f77])).

fof(f77,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f277,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl3_41
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f56,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f28,f32])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f28,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_6
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f436,plain,
    ( ~ spl3_44
    | spl3_22
    | ~ spl3_35
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f435,f417,f236,f159,f303])).

fof(f303,plain,
    ( spl3_44
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f159,plain,
    ( spl3_22
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f236,plain,
    ( spl3_35
  <=> ! [X1] :
        ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f435,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_22
    | ~ spl3_35
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f434,f160])).

fof(f160,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f159])).

fof(f434,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_35
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f429])).

fof(f429,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_35
    | ~ spl3_61 ),
    inference(superposition,[],[f237,f418])).

fof(f237,plain,
    ( ! [X1] :
        ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f236])).

fof(f419,plain,
    ( ~ spl3_44
    | spl3_61
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_52
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f407,f400,f362,f168,f72,f68,f64,f417,f303])).

fof(f168,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f362,plain,
    ( spl3_52
  <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f400,plain,
    ( spl3_58
  <=> k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f407,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_52
    | ~ spl3_58 ),
    inference(forward_demodulation,[],[f406,f363])).

fof(f363,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f362])).

fof(f406,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f405,f65])).

fof(f405,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f404,f73])).

fof(f404,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_24
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f403,f69])).

fof(f403,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_24
    | ~ spl3_58 ),
    inference(superposition,[],[f401,f169])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f401,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f400])).

fof(f402,plain,
    ( spl3_58
    | ~ spl3_5
    | ~ spl3_34
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f385,f381,f232,f76,f400])).

fof(f232,plain,
    ( spl3_34
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f381,plain,
    ( spl3_56
  <=> ! [X0] :
        ( k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f385,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_34
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f384,f233])).

fof(f233,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f232])).

fof(f384,plain,
    ( k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_56 ),
    inference(resolution,[],[f382,f77])).

fof(f382,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0)))) )
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f381])).

fof(f383,plain,
    ( spl3_56
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f367,f358,f95,f72,f381])).

fof(f95,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f358,plain,
    ( spl3_51
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f367,plain,
    ( ! [X0] :
        ( k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_51 ),
    inference(subsumption_resolution,[],[f365,f73])).

fof(f365,plain,
    ( ! [X0] :
        ( k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_9
    | ~ spl3_51 ),
    inference(resolution,[],[f359,f96])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f359,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1))) )
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f358])).

fof(f364,plain,
    ( spl3_52
    | spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f345,f337,f189,f76,f72,f68,f64,f60,f362])).

fof(f60,plain,
    ( spl3_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f189,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f337,plain,
    ( spl3_48
  <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f345,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f344,f65])).

fof(f344,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f343,f77])).

fof(f343,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f342,f61])).

fof(f61,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f342,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f341,f73])).

fof(f341,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f340,f69])).

fof(f340,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl3_26
    | ~ spl3_48 ),
    inference(superposition,[],[f338,f190])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f189])).

fof(f338,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f337])).

fof(f360,plain,
    ( spl3_51
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f313,f307,f72,f68,f64,f358])).

fof(f307,plain,
    ( spl3_45
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f313,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1))) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f312,f69])).

fof(f312,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1))) )
    | spl3_2
    | ~ spl3_4
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f311,f73])).

fof(f311,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1))) )
    | spl3_2
    | ~ spl3_45 ),
    inference(resolution,[],[f308,f65])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1))) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f307])).

fof(f339,plain,
    ( spl3_48
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_27
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f270,f263,f193,f76,f72,f68,f64,f337])).

fof(f193,plain,
    ( spl3_27
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f263,plain,
    ( spl3_39
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f270,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_27
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f269,f194])).

fof(f194,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f193])).

fof(f269,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f268,f65])).

fof(f268,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f267,f69])).

fof(f267,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f266,f73])).

fof(f266,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl3_5
    | ~ spl3_39 ),
    inference(resolution,[],[f264,f77])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f263])).

fof(f320,plain,
    ( spl3_6
    | ~ spl3_22
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f152,f146,f103,f76,f72,f159,f80])).

fof(f103,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v3_pre_topc(sK2(X0,X1),X0)
        | v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f146,plain,
    ( spl3_20
  <=> u1_struct_0(sK1) = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f152,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f151,f73])).

fof(f151,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f150,f77])).

fof(f150,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(superposition,[],[f104,f147])).

fof(f147,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f146])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK2(X0,X1),X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tsep_1(X1,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f319,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | spl3_44 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | spl3_44 ),
    inference(subsumption_resolution,[],[f317,f73])).

fof(f317,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_5
    | ~ spl3_9
    | spl3_44 ),
    inference(subsumption_resolution,[],[f315,f77])).

fof(f315,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_9
    | spl3_44 ),
    inference(resolution,[],[f304,f96])).

fof(f304,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f303])).

fof(f309,plain,
    ( spl3_45
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f144,f137,f129,f91,f307])).

fof(f91,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f129,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f137,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1))) )
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f143,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(k6_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f137])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ l1_pre_topc(k6_tmap_1(X0,X1))
        | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1))) )
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(resolution,[],[f130,f92])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ v1_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(k6_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f129])).

fof(f278,plain,
    ( spl3_41
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f220,f205,f99,f95,f276])).

fof(f99,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v3_pre_topc(u1_struct_0(X1),X0)
        | ~ v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f205,plain,
    ( spl3_29
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
        | ~ v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

% (21637)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f219,f96])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
    | ~ spl3_10
    | ~ spl3_29 ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0) )
    | ~ spl3_10
    | ~ spl3_29 ),
    inference(resolution,[],[f206,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(u1_struct_0(X1),X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
        | v2_struct_0(X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f205])).

fof(f265,plain,
    ( spl3_39
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f123,f115,f107,f91,f263])).

fof(f107,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f115,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) )
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f122,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(k8_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(k8_tmap_1(X0,X1))
        | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))) )
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(resolution,[],[f108,f92])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(k8_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f238,plain,
    ( spl3_35
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f216,f201,f83,f72,f68,f64,f236])).

fof(f83,plain,
    ( spl3_7
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f201,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
        | v3_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f216,plain,
    ( ! [X1] :
        ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X1,sK0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f215,f84])).

fof(f84,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f215,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
        | v3_pre_topc(X1,sK0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f214,f73])).

fof(f214,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
        | v3_pre_topc(X1,sK0) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f213,f69])).

fof(f213,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
        | v3_pre_topc(X1,sK0) )
    | spl3_2
    | ~ spl3_28 ),
    inference(resolution,[],[f202,f65])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
        | v3_pre_topc(X1,X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f201])).

fof(f234,plain,
    ( spl3_34
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f217,f209,f76,f232])).

fof(f209,plain,
    ( spl3_30
  <=> ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f217,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl3_5
    | ~ spl3_30 ),
    inference(resolution,[],[f210,f77])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl3_30
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f186,f176,f95,f72,f209])).

fof(f176,plain,
    ( spl3_25
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f186,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f184,f73])).

fof(f184,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_9
    | ~ spl3_25 ),
    inference(resolution,[],[f177,f96])).

fof(f177,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f176])).

fof(f207,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f45,f205])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f203,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f44,f201])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f195,plain,
    ( spl3_27
    | spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f183,f163,f76,f72,f68,f64,f60,f193])).

fof(f163,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f183,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f182,f65])).

fof(f182,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f181,f61])).

fof(f181,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f180,f73])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f179,f69])).

fof(f179,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(resolution,[],[f164,f77])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f191,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f58,f189])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f178,plain,
    ( spl3_25
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f174,f155,f72,f68,f64,f176])).

fof(f155,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f174,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f173,f73])).

% (21644)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f173,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | spl3_2
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f172,f69])).

fof(f172,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | spl3_2
    | ~ spl3_21 ),
    inference(resolution,[],[f156,f65])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f170,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f43,f168])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f165,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f47,f163])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f157,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f42,f155])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f148,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f142,f119,f80,f76,f72,f146])).

fof(f119,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | u1_struct_0(X1) = sK2(X0,X1)
        | v1_tsep_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f142,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f141,f73])).

fof(f141,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5
    | spl3_6
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f140,f77])).

fof(f140,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_6
    | ~ spl3_15 ),
    inference(resolution,[],[f120,f88])).

fof(f88,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | u1_struct_0(X1) = sK2(X0,X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f139,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f53,f137])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f131,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f51,f129])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f40,f119])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f117,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f50,f115])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f109,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f48,f107])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f41,f103])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f57,f99])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f93,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f85,plain,
    ( spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f29,f83,f80])).

fof(f29,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f74,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:30:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (21645)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.45  % (21638)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (21645)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (21643)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f458,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f62,f66,f70,f74,f78,f85,f93,f97,f101,f105,f109,f117,f121,f131,f139,f148,f157,f165,f170,f178,f191,f195,f203,f207,f211,f234,f238,f265,f278,f309,f319,f320,f339,f360,f364,f383,f402,f419,f436,f457])).
% 0.22/0.48  fof(f457,plain,(
% 0.22/0.48    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_41 | ~spl3_61),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f456])).
% 0.22/0.48  fof(f456,plain,(
% 0.22/0.48    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_41 | ~spl3_61)),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f438])).
% 0.22/0.48  fof(f438,plain,(
% 0.22/0.48    ~v1_tsep_1(sK1,sK0) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_41 | ~spl3_61)),
% 0.22/0.48    inference(subsumption_resolution,[],[f56,f437])).
% 0.22/0.48  fof(f437,plain,(
% 0.22/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_41 | ~spl3_61)),
% 0.22/0.48    inference(forward_demodulation,[],[f282,f418])).
% 0.22/0.48  fof(f418,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl3_61),
% 0.22/0.48    inference(avatar_component_clause,[],[f417])).
% 0.22/0.48  fof(f417,plain,(
% 0.22/0.48    spl3_61 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.22/0.48  fof(f282,plain,(
% 0.22/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_tsep_1(sK1,sK0) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_41)),
% 0.22/0.48    inference(subsumption_resolution,[],[f281,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    v2_pre_topc(sK0) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_3 <=> v2_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f281,plain,(
% 0.22/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | ~v1_tsep_1(sK1,sK0) | (spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_41)),
% 0.22/0.48    inference(subsumption_resolution,[],[f280,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~v2_struct_0(sK0) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl3_2 <=> v2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f280,plain,(
% 0.22/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v1_tsep_1(sK1,sK0) | (~spl3_4 | ~spl3_5 | ~spl3_41)),
% 0.22/0.48    inference(subsumption_resolution,[],[f279,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f279,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v1_tsep_1(sK1,sK0) | (~spl3_5 | ~spl3_41)),
% 0.22/0.48    inference(resolution,[],[f277,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    m1_pre_topc(sK1,sK0) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl3_5 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f277,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tsep_1(X1,X0)) ) | ~spl3_41),
% 0.22/0.48    inference(avatar_component_clause,[],[f276])).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    spl3_41 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f28,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    m1_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    v1_tsep_1(sK1,sK0) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl3_6 <=> v1_tsep_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f436,plain,(
% 0.22/0.48    ~spl3_44 | spl3_22 | ~spl3_35 | ~spl3_61),
% 0.22/0.48    inference(avatar_split_clause,[],[f435,f417,f236,f159,f303])).
% 0.22/0.48  fof(f303,plain,(
% 0.22/0.48    spl3_44 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    spl3_22 <=> v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.48  fof(f236,plain,(
% 0.22/0.48    spl3_35 <=> ! [X1] : (k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.48  fof(f435,plain,(
% 0.22/0.48    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_22 | ~spl3_35 | ~spl3_61)),
% 0.22/0.48    inference(subsumption_resolution,[],[f434,f160])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    ~v3_pre_topc(u1_struct_0(sK1),sK0) | spl3_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f159])).
% 0.22/0.48  fof(f434,plain,(
% 0.22/0.48    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_35 | ~spl3_61)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f429])).
% 0.22/0.48  fof(f429,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_35 | ~spl3_61)),
% 0.22/0.48    inference(superposition,[],[f237,f418])).
% 0.22/0.48  fof(f237,plain,(
% 0.22/0.48    ( ! [X1] : (k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) ) | ~spl3_35),
% 0.22/0.48    inference(avatar_component_clause,[],[f236])).
% 0.22/0.48  fof(f419,plain,(
% 0.22/0.48    ~spl3_44 | spl3_61 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_24 | ~spl3_52 | ~spl3_58),
% 0.22/0.48    inference(avatar_split_clause,[],[f407,f400,f362,f168,f72,f68,f64,f417,f303])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    spl3_24 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.48  fof(f362,plain,(
% 0.22/0.48    spl3_52 <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.22/0.48  fof(f400,plain,(
% 0.22/0.48    spl3_58 <=> k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.22/0.48  fof(f407,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_24 | ~spl3_52 | ~spl3_58)),
% 0.22/0.48    inference(forward_demodulation,[],[f406,f363])).
% 0.22/0.48  fof(f363,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~spl3_52),
% 0.22/0.48    inference(avatar_component_clause,[],[f362])).
% 0.22/0.48  fof(f406,plain,(
% 0.22/0.48    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_24 | ~spl3_58)),
% 0.22/0.48    inference(subsumption_resolution,[],[f405,f65])).
% 0.22/0.48  fof(f405,plain,(
% 0.22/0.48    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_24 | ~spl3_58)),
% 0.22/0.48    inference(subsumption_resolution,[],[f404,f73])).
% 0.22/0.48  fof(f404,plain,(
% 0.22/0.48    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_24 | ~spl3_58)),
% 0.22/0.48    inference(subsumption_resolution,[],[f403,f69])).
% 0.22/0.48  fof(f403,plain,(
% 0.22/0.48    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl3_24 | ~spl3_58)),
% 0.22/0.48    inference(superposition,[],[f401,f169])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl3_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f168])).
% 0.22/0.48  fof(f401,plain,(
% 0.22/0.48    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))) | ~spl3_58),
% 0.22/0.48    inference(avatar_component_clause,[],[f400])).
% 0.22/0.48  fof(f402,plain,(
% 0.22/0.48    spl3_58 | ~spl3_5 | ~spl3_34 | ~spl3_56),
% 0.22/0.48    inference(avatar_split_clause,[],[f385,f381,f232,f76,f400])).
% 0.22/0.48  fof(f232,plain,(
% 0.22/0.48    spl3_34 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.48  fof(f381,plain,(
% 0.22/0.48    spl3_56 <=> ! [X0] : (k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.48  fof(f385,plain,(
% 0.22/0.48    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))) | (~spl3_5 | ~spl3_34 | ~spl3_56)),
% 0.22/0.48    inference(forward_demodulation,[],[f384,f233])).
% 0.22/0.48  fof(f233,plain,(
% 0.22/0.48    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl3_34),
% 0.22/0.48    inference(avatar_component_clause,[],[f232])).
% 0.22/0.48  fof(f384,plain,(
% 0.22/0.48    k6_tmap_1(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))) | (~spl3_5 | ~spl3_56)),
% 0.22/0.48    inference(resolution,[],[f382,f77])).
% 0.22/0.48  fof(f382,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0))))) ) | ~spl3_56),
% 0.22/0.48    inference(avatar_component_clause,[],[f381])).
% 0.22/0.48  fof(f383,plain,(
% 0.22/0.48    spl3_56 | ~spl3_4 | ~spl3_9 | ~spl3_51),
% 0.22/0.48    inference(avatar_split_clause,[],[f367,f358,f95,f72,f381])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl3_9 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f358,plain,(
% 0.22/0.48    spl3_51 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.22/0.48  fof(f367,plain,(
% 0.22/0.48    ( ! [X0] : (k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0)) ) | (~spl3_4 | ~spl3_9 | ~spl3_51)),
% 0.22/0.48    inference(subsumption_resolution,[],[f365,f73])).
% 0.22/0.48  fof(f365,plain,(
% 0.22/0.48    ( ! [X0] : (k6_tmap_1(sK0,u1_struct_0(X0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_9 | ~spl3_51)),
% 0.22/0.48    inference(resolution,[],[f359,f96])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f359,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1)))) ) | ~spl3_51),
% 0.22/0.48    inference(avatar_component_clause,[],[f358])).
% 0.22/0.48  fof(f364,plain,(
% 0.22/0.48    spl3_52 | spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_26 | ~spl3_48),
% 0.22/0.48    inference(avatar_split_clause,[],[f345,f337,f189,f76,f72,f68,f64,f60,f362])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl3_1 <=> v2_struct_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f189,plain,(
% 0.22/0.48    spl3_26 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.48  fof(f337,plain,(
% 0.22/0.48    spl3_48 <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.48  fof(f345,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | (spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_26 | ~spl3_48)),
% 0.22/0.48    inference(subsumption_resolution,[],[f344,f65])).
% 0.22/0.48  fof(f344,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_26 | ~spl3_48)),
% 0.22/0.48    inference(subsumption_resolution,[],[f343,f77])).
% 0.22/0.48  fof(f343,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_26 | ~spl3_48)),
% 0.22/0.48    inference(subsumption_resolution,[],[f342,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ~v2_struct_0(sK1) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f60])).
% 0.22/0.48  fof(f342,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_26 | ~spl3_48)),
% 0.22/0.48    inference(subsumption_resolution,[],[f341,f73])).
% 0.22/0.48  fof(f341,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl3_3 | ~spl3_26 | ~spl3_48)),
% 0.22/0.48    inference(subsumption_resolution,[],[f340,f69])).
% 0.22/0.48  fof(f340,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | (~spl3_26 | ~spl3_48)),
% 0.22/0.48    inference(superposition,[],[f338,f190])).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    ( ! [X0,X1] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) ) | ~spl3_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f189])).
% 0.22/0.48  fof(f338,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) | ~spl3_48),
% 0.22/0.48    inference(avatar_component_clause,[],[f337])).
% 0.22/0.48  fof(f360,plain,(
% 0.22/0.48    spl3_51 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_45),
% 0.22/0.48    inference(avatar_split_clause,[],[f313,f307,f72,f68,f64,f358])).
% 0.22/0.48  fof(f307,plain,(
% 0.22/0.48    spl3_45 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.48  fof(f313,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1)))) ) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_45)),
% 0.22/0.48    inference(subsumption_resolution,[],[f312,f69])).
% 0.22/0.48  fof(f312,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1)))) ) | (spl3_2 | ~spl3_4 | ~spl3_45)),
% 0.22/0.48    inference(subsumption_resolution,[],[f311,f73])).
% 0.22/0.48  fof(f311,plain,(
% 0.22/0.48    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X1)),u1_pre_topc(k6_tmap_1(sK0,X1)))) ) | (spl3_2 | ~spl3_45)),
% 0.22/0.48    inference(resolution,[],[f308,f65])).
% 0.22/0.48  fof(f308,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1)))) ) | ~spl3_45),
% 0.22/0.48    inference(avatar_component_clause,[],[f307])).
% 0.22/0.48  fof(f339,plain,(
% 0.22/0.48    spl3_48 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_27 | ~spl3_39),
% 0.22/0.48    inference(avatar_split_clause,[],[f270,f263,f193,f76,f72,f68,f64,f337])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    spl3_27 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.48  fof(f263,plain,(
% 0.22/0.48    spl3_39 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.48  fof(f270,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_27 | ~spl3_39)),
% 0.22/0.48    inference(forward_demodulation,[],[f269,f194])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl3_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f193])).
% 0.22/0.48  fof(f269,plain,(
% 0.22/0.48    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_39)),
% 0.22/0.48    inference(subsumption_resolution,[],[f268,f65])).
% 0.22/0.48  fof(f268,plain,(
% 0.22/0.48    v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_39)),
% 0.22/0.48    inference(subsumption_resolution,[],[f267,f69])).
% 0.22/0.48  fof(f267,plain,(
% 0.22/0.48    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (~spl3_4 | ~spl3_5 | ~spl3_39)),
% 0.22/0.48    inference(subsumption_resolution,[],[f266,f73])).
% 0.22/0.48  fof(f266,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (~spl3_5 | ~spl3_39)),
% 0.22/0.48    inference(resolution,[],[f264,f77])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))) ) | ~spl3_39),
% 0.22/0.48    inference(avatar_component_clause,[],[f263])).
% 0.22/0.48  fof(f320,plain,(
% 0.22/0.48    spl3_6 | ~spl3_22 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_20),
% 0.22/0.48    inference(avatar_split_clause,[],[f152,f146,f103,f76,f72,f159,f80])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    spl3_11 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | v1_tsep_1(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    spl3_20 <=> u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_20)),
% 0.22/0.48    inference(subsumption_resolution,[],[f151,f73])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0) | (~spl3_5 | ~spl3_11 | ~spl3_20)),
% 0.22/0.48    inference(subsumption_resolution,[],[f150,f77])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0) | (~spl3_11 | ~spl3_20)),
% 0.22/0.48    inference(superposition,[],[f104,f147])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    u1_struct_0(sK1) = sK2(sK0,sK1) | ~spl3_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f146])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0)) ) | ~spl3_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f103])).
% 0.22/0.48  fof(f319,plain,(
% 0.22/0.48    ~spl3_4 | ~spl3_5 | ~spl3_9 | spl3_44),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f318])).
% 0.22/0.48  fof(f318,plain,(
% 0.22/0.48    $false | (~spl3_4 | ~spl3_5 | ~spl3_9 | spl3_44)),
% 0.22/0.48    inference(subsumption_resolution,[],[f317,f73])).
% 0.22/0.48  fof(f317,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | (~spl3_5 | ~spl3_9 | spl3_44)),
% 0.22/0.48    inference(subsumption_resolution,[],[f315,f77])).
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_9 | spl3_44)),
% 0.22/0.48    inference(resolution,[],[f304,f96])).
% 0.22/0.48  fof(f304,plain,(
% 0.22/0.48    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_44),
% 0.22/0.48    inference(avatar_component_clause,[],[f303])).
% 0.22/0.48  fof(f309,plain,(
% 0.22/0.48    spl3_45 | ~spl3_8 | ~spl3_17 | ~spl3_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f144,f137,f129,f91,f307])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl3_8 <=> ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    spl3_17 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k6_tmap_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    spl3_19 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1)))) ) | (~spl3_8 | ~spl3_17 | ~spl3_19)),
% 0.22/0.48    inference(subsumption_resolution,[],[f143,f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl3_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f137])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~l1_pre_topc(k6_tmap_1(X0,X1)) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k6_tmap_1(X0,X1)),u1_pre_topc(k6_tmap_1(X0,X1)))) ) | (~spl3_8 | ~spl3_17)),
% 0.22/0.48    inference(resolution,[],[f130,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) ) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f91])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_pre_topc(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl3_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f129])).
% 0.22/0.48  fof(f278,plain,(
% 0.22/0.48    spl3_41 | ~spl3_9 | ~spl3_10 | ~spl3_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f220,f205,f99,f95,f276])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl3_10 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    spl3_29 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.48  % (21637)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) ) | (~spl3_9 | ~spl3_10 | ~spl3_29)),
% 0.22/0.48    inference(subsumption_resolution,[],[f219,f96])).
% 0.22/0.48  fof(f219,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) ) | (~spl3_10 | ~spl3_29)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f218])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0)) ) | (~spl3_10 | ~spl3_29)),
% 0.22/0.48    inference(resolution,[],[f206,f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0)) ) | ~spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f99])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v2_struct_0(X0)) ) | ~spl3_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f205])).
% 0.22/0.48  fof(f265,plain,(
% 0.22/0.48    spl3_39 | ~spl3_8 | ~spl3_12 | ~spl3_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f123,f115,f107,f91,f263])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl3_12 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    spl3_14 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))) ) | (~spl3_8 | ~spl3_12 | ~spl3_14)),
% 0.22/0.48    inference(subsumption_resolution,[],[f122,f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) ) | ~spl3_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f115])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | k8_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(k8_tmap_1(X0,X1)),u1_pre_topc(k8_tmap_1(X0,X1)))) ) | (~spl3_8 | ~spl3_12)),
% 0.22/0.48    inference(resolution,[],[f108,f92])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) ) | ~spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f107])).
% 0.22/0.48  fof(f238,plain,(
% 0.22/0.48    spl3_35 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f216,f201,f83,f72,f68,f64,f236])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl3_7 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    spl3_28 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.48  fof(f216,plain,(
% 0.22/0.48    ( ! [X1] : (k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) ) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7 | ~spl3_28)),
% 0.22/0.48    inference(forward_demodulation,[],[f215,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) ) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_28)),
% 0.22/0.48    inference(subsumption_resolution,[],[f214,f73])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) ) | (spl3_2 | ~spl3_3 | ~spl3_28)),
% 0.22/0.48    inference(subsumption_resolution,[],[f213,f69])).
% 0.22/0.48  fof(f213,plain,(
% 0.22/0.48    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) ) | (spl3_2 | ~spl3_28)),
% 0.22/0.48    inference(resolution,[],[f202,f65])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) ) | ~spl3_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f201])).
% 0.22/0.48  fof(f234,plain,(
% 0.22/0.48    spl3_34 | ~spl3_5 | ~spl3_30),
% 0.22/0.48    inference(avatar_split_clause,[],[f217,f209,f76,f232])).
% 0.22/0.48  fof(f209,plain,(
% 0.22/0.48    spl3_30 <=> ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.48  fof(f217,plain,(
% 0.22/0.48    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl3_5 | ~spl3_30)),
% 0.22/0.48    inference(resolution,[],[f210,f77])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) ) | ~spl3_30),
% 0.22/0.48    inference(avatar_component_clause,[],[f209])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    spl3_30 | ~spl3_4 | ~spl3_9 | ~spl3_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f186,f176,f95,f72,f209])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    spl3_25 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) ) | (~spl3_4 | ~spl3_9 | ~spl3_25)),
% 0.22/0.48    inference(subsumption_resolution,[],[f184,f73])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (~spl3_9 | ~spl3_25)),
% 0.22/0.48    inference(resolution,[],[f177,f96])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | ~spl3_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f176])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    spl3_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f45,f205])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    spl3_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f44,f201])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    spl3_27 | spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_23),
% 0.22/0.48    inference(avatar_split_clause,[],[f183,f163,f76,f72,f68,f64,f60,f193])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    spl3_23 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (spl3_1 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_23)),
% 0.22/0.48    inference(subsumption_resolution,[],[f182,f65])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_23)),
% 0.22/0.48    inference(subsumption_resolution,[],[f181,f61])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_23)),
% 0.22/0.48    inference(subsumption_resolution,[],[f180,f73])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl3_3 | ~spl3_5 | ~spl3_23)),
% 0.22/0.48    inference(subsumption_resolution,[],[f179,f69])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl3_5 | ~spl3_23)),
% 0.22/0.48    inference(resolution,[],[f164,f77])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) ) | ~spl3_23),
% 0.22/0.48    inference(avatar_component_clause,[],[f163])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    spl3_26),
% 0.22/0.48    inference(avatar_split_clause,[],[f58,f189])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f55,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    spl3_25 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_21),
% 0.22/0.48    inference(avatar_split_clause,[],[f174,f155,f72,f68,f64,f176])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl3_21 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_21)),
% 0.22/0.48    inference(subsumption_resolution,[],[f173,f73])).
% 0.22/0.49  % (21644)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | (spl3_2 | ~spl3_3 | ~spl3_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f172,f69])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | (spl3_2 | ~spl3_21)),
% 0.22/0.49    inference(resolution,[],[f156,f65])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) ) | ~spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    spl3_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f168])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    spl3_23),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f163])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    spl3_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f155])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    spl3_20 | ~spl3_4 | ~spl3_5 | spl3_6 | ~spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f142,f119,f80,f76,f72,f146])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    spl3_15 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tsep_1(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    u1_struct_0(sK1) = sK2(sK0,sK1) | (~spl3_4 | ~spl3_5 | spl3_6 | ~spl3_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f141,f73])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    u1_struct_0(sK1) = sK2(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_5 | spl3_6 | ~spl3_15)),
% 0.22/0.49    inference(subsumption_resolution,[],[f140,f77])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~m1_pre_topc(sK1,sK0) | u1_struct_0(sK1) = sK2(sK0,sK1) | ~l1_pre_topc(sK0) | (spl3_6 | ~spl3_15)),
% 0.22/0.49    inference(resolution,[],[f120,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~v1_tsep_1(sK1,sK0) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~l1_pre_topc(X0)) ) | ~spl3_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f119])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    spl3_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f53,f137])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl3_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f129])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f119])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tsep_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f50,f115])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f107])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f103])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_pre_topc(sK2(X0,X1),X0) | v1_tsep_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f57,f99])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f54,f37])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f95])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f91])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl3_6 | spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f83,f80])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f76])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f72])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f68])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f64])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ~spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f60])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (21645)------------------------------
% 0.22/0.49  % (21645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21645)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (21645)Memory used [KB]: 10874
% 0.22/0.49  % (21645)Time elapsed: 0.078 s
% 0.22/0.49  % (21645)------------------------------
% 0.22/0.49  % (21645)------------------------------
% 0.22/0.49  % (21635)Success in time 0.122 s
%------------------------------------------------------------------------------
