%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:30 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  373 ( 840 expanded)
%              Number of leaves         :   55 ( 322 expanded)
%              Depth                    :   31
%              Number of atoms          : 2145 (3484 expanded)
%              Number of equality atoms :  114 ( 345 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f110,f115,f138,f160,f167,f190,f221,f232,f272,f285,f339,f468,f473,f626,f667,f674,f757,f758,f990,f1016,f1179,f1185,f1219,f1253,f1359,f1387,f1404,f1541,f1981,f2094,f2138,f2139,f2493,f2745,f2963,f2985,f3268])).

fof(f3268,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46
    | ~ spl4_54
    | ~ spl4_56
    | ~ spl4_121 ),
    inference(avatar_contradiction_clause,[],[f3267])).

fof(f3267,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46
    | ~ spl4_54
    | ~ spl4_56
    | ~ spl4_121 ),
    inference(subsumption_resolution,[],[f2998,f933])).

fof(f933,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl4_54
  <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f2998,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46
    | ~ spl4_56
    | ~ spl4_121 ),
    inference(forward_demodulation,[],[f2997,f324])).

fof(f324,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl4_19
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f2997,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46
    | ~ spl4_56
    | ~ spl4_121 ),
    inference(subsumption_resolution,[],[f2996,f2744])).

fof(f2744,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_121 ),
    inference(avatar_component_clause,[],[f2742])).

fof(f2742,plain,
    ( spl4_121
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).

fof(f2996,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f2995,f324])).

fof(f2995,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f2994,f231])).

fof(f231,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_15
  <=> u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f2994,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f2993,f1177])).

fof(f1177,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f1175])).

fof(f1175,plain,
    ( spl4_56
  <=> v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f2993,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46 ),
    inference(forward_demodulation,[],[f2992,f324])).

fof(f2992,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46 ),
    inference(forward_demodulation,[],[f2991,f231])).

fof(f2991,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46 ),
    inference(subsumption_resolution,[],[f2990,f205])).

fof(f205,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_13
  <=> v1_funct_1(k6_partfun1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f2990,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_19
    | ~ spl4_41
    | spl4_46 ),
    inference(subsumption_resolution,[],[f2701,f634])).

fof(f634,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl4_41
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f2701,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_19
    | spl4_46 ),
    inference(resolution,[],[f2419,f729])).

fof(f729,plain,
    ( ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl4_46
  <=> sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f2419,plain,
    ( ! [X61,X60] :
        ( sP2(X61,X60,sK0)
        | ~ v1_funct_2(X61,k1_xboole_0,u1_struct_0(X60))
        | ~ l1_pre_topc(X60)
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X60))))
        | ~ v5_pre_topc(X61,sK0,X60) )
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f2418,f324])).

fof(f2418,plain,
    ( ! [X61,X60] :
        ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X60))))
        | ~ v1_funct_2(X61,k1_xboole_0,u1_struct_0(X60))
        | ~ l1_pre_topc(X60)
        | ~ v1_funct_1(X61)
        | sP2(X61,X60,sK0)
        | ~ v5_pre_topc(X61,sK0,X60) )
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f2417,f137])).

fof(f137,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f2417,plain,
    ( ! [X61,X60] :
        ( ~ v1_funct_2(X61,k1_xboole_0,u1_struct_0(X60))
        | ~ l1_pre_topc(X60)
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60))))
        | sP2(X61,X60,sK0)
        | ~ v5_pre_topc(X61,sK0,X60) )
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f2416,f324])).

fof(f2416,plain,
    ( ! [X61,X60] :
        ( ~ v1_funct_2(X61,k2_struct_0(sK0),u1_struct_0(X60))
        | ~ l1_pre_topc(X60)
        | ~ v1_funct_1(X61)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60))))
        | sP2(X61,X60,sK0)
        | ~ v5_pre_topc(X61,sK0,X60) )
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f2415,f137])).

fof(f2415,plain,
    ( ! [X61,X60] :
        ( ~ l1_pre_topc(X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,u1_struct_0(sK0),u1_struct_0(X60))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60))))
        | sP2(X61,X60,sK0)
        | ~ v5_pre_topc(X61,sK0,X60) )
    | ~ spl4_3
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f2406,f95])).

fof(f95,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2406,plain,
    ( ! [X61,X60] :
        ( ~ l1_pre_topc(X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,u1_struct_0(sK0),u1_struct_0(X60))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60))))
        | ~ l1_pre_topc(sK0)
        | sP2(X61,X60,sK0)
        | ~ v5_pre_topc(X61,sK0,X60) )
    | ~ spl4_19 ),
    inference(trivial_inequality_removal,[],[f2403])).

fof(f2403,plain,
    ( ! [X61,X60] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ l1_pre_topc(X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,u1_struct_0(sK0),u1_struct_0(X60))
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60))))
        | ~ l1_pre_topc(sK0)
        | sP2(X61,X60,sK0)
        | ~ v5_pre_topc(X61,sK0,X60) )
    | ~ spl4_19 ),
    inference(superposition,[],[f58,f324])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | sP2(X2,X1,X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f2985,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2963,plain,
    ( ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | ~ spl4_56
    | spl4_60
    | ~ spl4_99
    | ~ spl4_121 ),
    inference(avatar_contradiction_clause,[],[f2962])).

fof(f2962,plain,
    ( $false
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | ~ spl4_56
    | spl4_60
    | ~ spl4_99
    | ~ spl4_121 ),
    inference(subsumption_resolution,[],[f2961,f1177])).

fof(f2961,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60
    | ~ spl4_99
    | ~ spl4_121 ),
    inference(forward_demodulation,[],[f2960,f324])).

fof(f2960,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60
    | ~ spl4_99
    | ~ spl4_121 ),
    inference(forward_demodulation,[],[f2959,f231])).

fof(f2959,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60
    | ~ spl4_99
    | ~ spl4_121 ),
    inference(subsumption_resolution,[],[f2958,f2047])).

fof(f2047,plain,
    ( sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f2046])).

fof(f2046,plain,
    ( spl4_99
  <=> sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f2958,plain,
    ( ~ sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60
    | ~ spl4_121 ),
    inference(forward_demodulation,[],[f2957,f324])).

fof(f2957,plain,
    ( ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60
    | ~ spl4_121 ),
    inference(subsumption_resolution,[],[f2956,f2744])).

fof(f2956,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60 ),
    inference(forward_demodulation,[],[f2955,f324])).

fof(f2955,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60 ),
    inference(forward_demodulation,[],[f2954,f231])).

fof(f2954,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60 ),
    inference(subsumption_resolution,[],[f2953,f205])).

fof(f2953,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60 ),
    inference(subsumption_resolution,[],[f2950,f634])).

fof(f2950,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41
    | spl4_60 ),
    inference(resolution,[],[f2948,f1358])).

fof(f1358,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | spl4_60 ),
    inference(avatar_component_clause,[],[f1356])).

fof(f1356,plain,
    ( spl4_60
  <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f2948,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ sP2(X1,X0,k6_tmap_1(sK0,sK1))
        | ~ v1_funct_2(X1,k1_xboole_0,u1_struct_0(X0)) )
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f2947,f324])).

fof(f2947,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ sP2(X1,X0,k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f2946,f324])).

fof(f2946,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ sP2(X1,X0,k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_15
    | ~ spl4_19
    | ~ spl4_30
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f775,f324])).

fof(f775,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | k1_xboole_0 != k2_struct_0(sK0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ sP2(X1,X0,k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_15
    | ~ spl4_30
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f521,f634])).

fof(f521,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | k1_xboole_0 != k2_struct_0(sK0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
        | ~ sP2(X1,X0,k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f520,f231])).

fof(f520,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | k1_xboole_0 != k2_struct_0(sK0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X0))))
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
        | ~ sP2(X1,X0,k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_15
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f469,f231])).

fof(f469,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k2_struct_0(sK0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X0))))
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
        | ~ sP2(X1,X0,k6_tmap_1(sK0,sK1))
        | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_30 ),
    inference(superposition,[],[f57,f467])).

fof(f467,plain,
    ( k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f465])).

fof(f465,plain,
    ( spl4_30
  <=> k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) != k1_xboole_0
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | ~ sP2(X2,X1,X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2745,plain,
    ( spl4_121
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f2327,f454,f322,f2742])).

fof(f454,plain,
    ( spl4_28
  <=> m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f2327,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_19
    | ~ spl4_28 ),
    inference(superposition,[],[f455,f324])).

fof(f455,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f454])).

fof(f2493,plain,
    ( spl4_56
    | ~ spl4_19
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f2492,f1214,f322,f1175])).

fof(f1214,plain,
    ( spl4_58
  <=> v1_funct_2(k6_partfun1(k1_xboole_0),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f2492,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl4_19
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f1215,f324])).

fof(f1215,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f2139,plain,
    ( sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) != k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2138,plain,
    ( spl4_105
    | ~ spl4_28
    | ~ spl4_91 ),
    inference(avatar_split_clause,[],[f1997,f1978,f454,f2135])).

fof(f2135,plain,
    ( spl4_105
  <=> sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).

fof(f1978,plain,
    ( spl4_91
  <=> sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f1997,plain,
    ( sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ spl4_28
    | ~ spl4_91 ),
    inference(superposition,[],[f1980,f481])).

fof(f481,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)
    | ~ spl4_28 ),
    inference(resolution,[],[f455,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f1980,plain,
    ( sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ spl4_91 ),
    inference(avatar_component_clause,[],[f1978])).

fof(f2094,plain,
    ( spl4_61
    | spl4_103 ),
    inference(avatar_contradiction_clause,[],[f2093])).

fof(f2093,plain,
    ( $false
    | spl4_61
    | spl4_103 ),
    inference(subsumption_resolution,[],[f2092,f1386])).

fof(f1386,plain,
    ( ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | spl4_61 ),
    inference(avatar_component_clause,[],[f1384])).

fof(f1384,plain,
    ( spl4_61
  <=> sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f2092,plain,
    ( sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | spl4_103 ),
    inference(resolution,[],[f2090,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2),X1)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2090,plain,
    ( ~ v3_pre_topc(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | spl4_103 ),
    inference(avatar_component_clause,[],[f2088])).

fof(f2088,plain,
    ( spl4_103
  <=> v3_pre_topc(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).

fof(f1981,plain,
    ( spl4_91
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1415,f1401,f1978])).

fof(f1401,plain,
    ( spl4_62
  <=> m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1415,plain,
    ( sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ spl4_62 ),
    inference(resolution,[],[f1403,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f1403,plain,
    ( m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1541,plain,
    ( ~ spl4_69
    | ~ spl4_15
    | ~ spl4_28
    | spl4_61 ),
    inference(avatar_split_clause,[],[f1396,f1384,f454,f229,f1538])).

fof(f1538,plain,
    ( spl4_69
  <=> v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f1396,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | ~ spl4_15
    | ~ spl4_28
    | spl4_61 ),
    inference(forward_demodulation,[],[f1395,f481])).

fof(f1395,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | ~ spl4_15
    | spl4_61 ),
    inference(forward_demodulation,[],[f1391,f231])).

fof(f1391,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | ~ spl4_15
    | spl4_61 ),
    inference(resolution,[],[f1386,f241])).

fof(f241,plain,
    ( ! [X4,X3] :
        ( sP2(X4,k6_tmap_1(sK0,sK1),X3)
        | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X3),k2_struct_0(sK0),X4,sK3(X3,k6_tmap_1(sK0,sK1),X4)),X3) )
    | ~ spl4_15 ),
    inference(superposition,[],[f55,f231])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1404,plain,
    ( spl4_62
    | ~ spl4_15
    | spl4_61 ),
    inference(avatar_split_clause,[],[f1399,f1384,f229,f1401])).

fof(f1399,plain,
    ( m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_15
    | spl4_61 ),
    inference(forward_demodulation,[],[f1393,f231])).

fof(f1393,plain,
    ( m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | spl4_61 ),
    inference(resolution,[],[f1386,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1387,plain,
    ( ~ spl4_61
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28
    | spl4_36
    | ~ spl4_41
    | spl4_60 ),
    inference(avatar_split_clause,[],[f1381,f1356,f633,f512,f454,f282,f229,f203,f1384])).

fof(f282,plain,
    ( spl4_18
  <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f512,plain,
    ( spl4_36
  <=> k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f1381,plain,
    ( ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28
    | spl4_36
    | ~ spl4_41
    | spl4_60 ),
    inference(subsumption_resolution,[],[f1380,f455])).

fof(f1380,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | spl4_36
    | ~ spl4_41
    | spl4_60 ),
    inference(forward_demodulation,[],[f1379,f231])).

fof(f1379,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | spl4_36
    | ~ spl4_41
    | spl4_60 ),
    inference(subsumption_resolution,[],[f1378,f284])).

fof(f284,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f282])).

fof(f1378,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | ~ spl4_15
    | spl4_36
    | ~ spl4_41
    | spl4_60 ),
    inference(forward_demodulation,[],[f1377,f231])).

fof(f1377,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | spl4_36
    | ~ spl4_41
    | spl4_60 ),
    inference(subsumption_resolution,[],[f1376,f513])).

fof(f513,plain,
    ( k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f512])).

fof(f1376,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | ~ spl4_41
    | spl4_60 ),
    inference(subsumption_resolution,[],[f1362,f634])).

fof(f1362,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | spl4_60 ),
    inference(duplicate_literal_removal,[],[f1361])).

fof(f1361,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | spl4_60 ),
    inference(resolution,[],[f1358,f443])).

fof(f443,plain,
    ( ! [X4,X5] :
        ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),X5,X4)
        | ~ l1_pre_topc(X5)
        | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(X5),u1_struct_0(X4))
        | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4))))
        | k1_xboole_0 = k2_struct_0(X4)
        | ~ sP2(k6_partfun1(k2_struct_0(sK0)),X4,X5)
        | ~ l1_pre_topc(X4) )
    | ~ spl4_13 ),
    inference(resolution,[],[f205,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ sP2(X2,X1,X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1359,plain,
    ( ~ spl4_60
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f1350,f637,f633,f454,f282,f269,f229,f218,f203,f135,f93,f88,f1356])).

fof(f88,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f218,plain,
    ( spl4_14
  <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f269,plain,
    ( spl4_17
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f637,plain,
    ( spl4_42
  <=> v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f1350,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1349,f271])).

fof(f271,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f269])).

fof(f1349,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1348,f137])).

fof(f1348,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1347,f455])).

fof(f1347,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1346,f231])).

fof(f1346,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1345,f271])).

fof(f1345,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1344,f137])).

fof(f1344,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1343,f231])).

fof(f1343,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1342,f284])).

fof(f1342,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1341,f231])).

fof(f1341,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1340,f271])).

fof(f1340,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1339,f137])).

fof(f1339,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1338,f231])).

fof(f1338,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1337,f455])).

fof(f1337,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1336,f137])).

fof(f1336,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1335,f231])).

fof(f1335,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1334,f284])).

fof(f1334,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1333,f137])).

fof(f1333,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1332,f231])).

fof(f1332,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | spl4_14
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1331,f95])).

fof(f1331,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1330,f90])).

fof(f90,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f1330,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13
    | spl4_14
    | ~ spl4_41
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1329,f634])).

fof(f1329,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13
    | spl4_14
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f1328,f638])).

fof(f638,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f637])).

fof(f1328,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_13
    | spl4_14 ),
    inference(resolution,[],[f441,f220])).

fof(f220,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f441,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),X0,X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_13 ),
    inference(resolution,[],[f205,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f1253,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(avatar_contradiction_clause,[],[f1252])).

fof(f1252,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(subsumption_resolution,[],[f1251,f455])).

fof(f1251,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(forward_demodulation,[],[f1250,f137])).

fof(f1250,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(forward_demodulation,[],[f1249,f231])).

fof(f1249,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(subsumption_resolution,[],[f1248,f284])).

fof(f1248,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(forward_demodulation,[],[f1247,f137])).

fof(f1247,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(forward_demodulation,[],[f1246,f231])).

fof(f1246,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(subsumption_resolution,[],[f1245,f219])).

fof(f219,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f1245,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_13
    | spl4_36
    | ~ spl4_41
    | spl4_46 ),
    inference(subsumption_resolution,[],[f1244,f634])).

fof(f1244,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_13
    | spl4_36
    | spl4_46 ),
    inference(subsumption_resolution,[],[f1243,f513])).

fof(f1243,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_13
    | spl4_46 ),
    inference(subsumption_resolution,[],[f1239,f95])).

fof(f1239,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_13
    | spl4_46 ),
    inference(resolution,[],[f729,f444])).

fof(f444,plain,
    ( ! [X6,X7] :
        ( sP2(k6_partfun1(k2_struct_0(sK0)),X6,X7)
        | ~ l1_pre_topc(X7)
        | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(X7),u1_struct_0(X6))
        | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6))))
        | k1_xboole_0 = k2_struct_0(X6)
        | ~ l1_pre_topc(X6)
        | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),X7,X6) )
    | ~ spl4_13 ),
    inference(resolution,[],[f205,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | sP2(X2,X1,X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1219,plain,
    ( k7_tmap_1(sK0,sK1) != k6_partfun1(k1_xboole_0)
    | k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0))
    | v1_funct_2(k6_partfun1(k1_xboole_0),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1185,plain,
    ( spl4_14
    | spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f1183,f187,f119,f218])).

fof(f119,plain,
    ( spl4_6
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f187,plain,
    ( spl4_12
  <=> k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1183,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1011,f120])).

fof(f120,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f1011,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f43,f189])).

fof(f189,plain,
    ( k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f187])).

fof(f43,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f1179,plain,
    ( k7_tmap_1(sK0,sK1) != k6_partfun1(k1_xboole_0)
    | k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1016,plain,
    ( spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f1015])).

fof(f1015,plain,
    ( $false
    | spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f1014,f728])).

fof(f728,plain,
    ( sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f727])).

fof(f1014,plain,
    ( ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0)
    | spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f698,f120])).

fof(f698,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0)
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(superposition,[],[f696,f166])).

fof(f166,plain,
    ( sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_11
  <=> sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f696,plain,
    ( ! [X0] :
        ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0)
        | ~ sP2(X0,k6_tmap_1(sK0,sK1),sK0) )
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(superposition,[],[f695,f137])).

fof(f695,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK0),X1,sK1),X0)
        | ~ sP2(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f627,f620])).

fof(f620,plain,
    ( v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl4_39
  <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f627,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK0),X1,sK1),X0)
        | ~ sP2(X1,k6_tmap_1(sK0,sK1),X0) )
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(resolution,[],[f243,f159])).

fof(f159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f243,plain,
    ( ! [X8,X7,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(X7,k6_tmap_1(sK0,sK1))
        | v3_pre_topc(k8_relset_1(u1_struct_0(X8),k2_struct_0(sK0),X9,X7),X8)
        | ~ sP2(X9,k6_tmap_1(sK0,sK1),X8) )
    | ~ spl4_15 ),
    inference(superposition,[],[f56,f231])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f990,plain,
    ( ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f986,f219])).

fof(f986,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f985,f455])).

fof(f985,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f984,f189])).

fof(f984,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f983,f137])).

fof(f983,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f982,f231])).

fof(f982,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f981,f189])).

fof(f981,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f980,f284])).

fof(f980,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f979,f189])).

fof(f979,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f978,f137])).

fof(f978,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f977,f231])).

fof(f977,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f976,f205])).

fof(f976,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f975,f189])).

fof(f975,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f40,f121])).

fof(f121,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f40,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f758,plain,
    ( k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
    | k2_struct_0(sK0) != k2_struct_0(k6_tmap_1(sK0,sK1))
    | k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0))
    | k7_tmap_1(sK0,sK1) = k6_partfun1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f757,plain,
    ( k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
    | k2_struct_0(sK0) != k2_struct_0(k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f674,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_42 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_42 ),
    inference(subsumption_resolution,[],[f672,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f672,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_42 ),
    inference(subsumption_resolution,[],[f671,f109])).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f671,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_42 ),
    inference(subsumption_resolution,[],[f670,f95])).

fof(f670,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | spl4_42 ),
    inference(subsumption_resolution,[],[f669,f90])).

fof(f669,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl4_42 ),
    inference(resolution,[],[f639,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f639,plain,
    ( ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f637])).

fof(f667,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f666])).

fof(f666,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | spl4_41 ),
    inference(subsumption_resolution,[],[f665,f159])).

fof(f665,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_41 ),
    inference(resolution,[],[f635,f170])).

fof(f170,plain,
    ( ! [X4] :
        ( l1_pre_topc(k6_tmap_1(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f169,f137])).

fof(f169,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k6_tmap_1(sK0,X4)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f168,f95])).

fof(f168,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k6_tmap_1(sK0,X4)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f101,f90])).

fof(f101,plain,
    ( ! [X4] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k6_tmap_1(sK0,X4)) )
    | spl4_1 ),
    inference(resolution,[],[f85,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f635,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f633])).

fof(f626,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f625])).

fof(f625,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15
    | spl4_39 ),
    inference(subsumption_resolution,[],[f624,f159])).

fof(f624,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15
    | spl4_39 ),
    inference(forward_demodulation,[],[f623,f231])).

fof(f623,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | spl4_39 ),
    inference(subsumption_resolution,[],[f622,f159])).

fof(f622,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | spl4_39 ),
    inference(resolution,[],[f619,f255])).

fof(f255,plain,
    ( ! [X7] :
        ( v3_pre_topc(X7,k6_tmap_1(sK0,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f254,f137])).

fof(f254,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7))))
        | v3_pre_topc(X7,k6_tmap_1(sK0,X7)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f253,f95])).

fof(f253,plain,
    ( ! [X7] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7))))
        | v3_pre_topc(X7,k6_tmap_1(sK0,X7)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f104,f90])).

fof(f104,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7))))
        | v3_pre_topc(X7,k6_tmap_1(sK0,X7)) )
    | spl4_1 ),
    inference(resolution,[],[f85,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | v3_pre_topc(X2,k6_tmap_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | X1 != X2
      | v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f619,plain,
    ( ~ v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f618])).

fof(f473,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | spl4_28 ),
    inference(subsumption_resolution,[],[f252,f456])).

fof(f456,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f454])).

fof(f252,plain,
    ( m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f251,f189])).

fof(f251,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f250,f231])).

fof(f250,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f236,f159])).

fof(f236,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6))))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f235,f137])).

fof(f235,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6))))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f234,f137])).

fof(f234,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6))))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f233,f95])).

fof(f233,plain,
    ( ! [X6] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6))))) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f103,f90])).

fof(f103,plain,
    ( ! [X6] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6))))) )
    | spl4_1 ),
    inference(resolution,[],[f85,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f468,plain,
    ( spl4_30
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f334,f229,f157,f135,f93,f88,f83,f465])).

fof(f334,plain,
    ( k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f333,f231])).

fof(f333,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f180,f159])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f171,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f171,plain,
    ( ! [X0] :
        ( l1_struct_0(k6_tmap_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f170,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f339,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12
    | spl4_13 ),
    inference(subsumption_resolution,[],[f330,f204])).

fof(f204,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f330,plain,
    ( v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f175,f189])).

fof(f175,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f174,f159])).

fof(f174,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_funct_1(k7_tmap_1(sK0,X5)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f173,f137])).

fof(f173,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_funct_1(k7_tmap_1(sK0,X5)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f172,f95])).

fof(f172,plain,
    ( ! [X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_funct_1(k7_tmap_1(sK0,X5)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f102,f90])).

fof(f102,plain,
    ( ! [X5] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_funct_1(k7_tmap_1(sK0,X5)) )
    | spl4_1 ),
    inference(resolution,[],[f85,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f285,plain,
    ( spl4_18
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f249,f229,f187,f135,f107,f93,f88,f83,f282])).

fof(f249,plain,
    ( v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f248,f189])).

fof(f248,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f247,f137])).

fof(f247,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f246,f85])).

fof(f246,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f245,f109])).

fof(f245,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f244,f95])).

fof(f244,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f237,f90])).

fof(f237,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_15 ),
    inference(superposition,[],[f74,f231])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f272,plain,
    ( spl4_17
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f227,f157,f135,f119,f93,f88,f83,f269])).

fof(f227,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f226,f121])).

fof(f226,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f225,f159])).

fof(f225,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | k6_tmap_1(sK0,X3) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
        | ~ v3_pre_topc(X3,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f224,f137])).

fof(f224,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3)
        | ~ v3_pre_topc(X3,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f223,f137])).

fof(f223,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3)
        | ~ v3_pre_topc(X3,sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f222,f95])).

fof(f222,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3)
        | ~ v3_pre_topc(X3,sK0) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f100,f90])).

fof(f100,plain,
    ( ! [X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3)
        | ~ v3_pre_topc(X3,sK0) )
    | spl4_1 ),
    inference(resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f232,plain,
    ( spl4_15
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f191,f157,f135,f93,f88,f83,f229])).

fof(f191,plain,
    ( u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f185,f159])).

fof(f185,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | u1_struct_0(k6_tmap_1(sK0,X1)) = k2_struct_0(sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f184,f137])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f183,f137])).

fof(f183,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f182,f95])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f98,f90])).

fof(f98,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) )
    | spl4_1 ),
    inference(resolution,[],[f85,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f221,plain,
    ( ~ spl4_14
    | spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f192,f187,f140,f218])).

fof(f140,plain,
    ( spl4_9
  <=> v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f192,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | spl4_9
    | ~ spl4_12 ),
    inference(superposition,[],[f141,f189])).

fof(f141,plain,
    ( ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f190,plain,
    ( spl4_12
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f181,f157,f135,f93,f88,f83,f187])).

fof(f181,plain,
    ( k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_10 ),
    inference(resolution,[],[f179,f159])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f178,f137])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f177,f137])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f176,f95])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f97,f90])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) )
    | spl4_1 ),
    inference(resolution,[],[f85,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f167,plain,
    ( spl4_11
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f162,f135,f107,f164])).

fof(f162,plain,
    ( sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f117,f137])).

fof(f117,plain,
    ( sK1 = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f109,f69])).

fof(f160,plain,
    ( spl4_10
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f144,f135,f107,f157])).

fof(f144,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(superposition,[],[f109,f137])).

fof(f138,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f127,f112,f135])).

fof(f112,plain,
    ( spl4_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f127,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f114,f49])).

fof(f114,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f105,f93,f112])).

fof(f105,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f95,f52])).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f107])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (27092)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (27084)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (27079)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (27086)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (27083)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (27093)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (27077)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (27080)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (27090)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (27094)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (27097)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (27095)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (27097)Refutation not found, incomplete strategy% (27097)------------------------------
% 0.20/0.51  % (27097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27082)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (27091)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (27096)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (27078)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (27089)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (27085)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (27089)Refutation not found, incomplete strategy% (27089)------------------------------
% 0.20/0.52  % (27089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27089)Memory used [KB]: 6140
% 0.20/0.52  % (27089)Time elapsed: 0.106 s
% 0.20/0.52  % (27089)------------------------------
% 0.20/0.52  % (27089)------------------------------
% 0.20/0.52  % (27081)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.31/0.52  % (27088)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.31/0.52  % (27077)Refutation not found, incomplete strategy% (27077)------------------------------
% 1.31/0.52  % (27077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.52  % (27077)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.52  
% 1.31/0.52  % (27077)Memory used [KB]: 6396
% 1.31/0.52  % (27077)Time elapsed: 0.104 s
% 1.31/0.52  % (27077)------------------------------
% 1.31/0.52  % (27077)------------------------------
% 1.31/0.52  % (27087)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.31/0.53  % (27078)Refutation not found, incomplete strategy% (27078)------------------------------
% 1.31/0.53  % (27078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (27078)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (27078)Memory used [KB]: 10618
% 1.31/0.53  % (27078)Time elapsed: 0.088 s
% 1.31/0.53  % (27078)------------------------------
% 1.31/0.53  % (27078)------------------------------
% 1.31/0.53  % (27087)Refutation not found, incomplete strategy% (27087)------------------------------
% 1.31/0.53  % (27087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (27087)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (27087)Memory used [KB]: 6140
% 1.31/0.53  % (27087)Time elapsed: 0.085 s
% 1.31/0.53  % (27087)------------------------------
% 1.31/0.53  % (27087)------------------------------
% 1.31/0.54  % (27097)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (27097)Memory used [KB]: 10618
% 1.31/0.54  % (27097)Time elapsed: 0.094 s
% 1.31/0.54  % (27097)------------------------------
% 1.31/0.54  % (27097)------------------------------
% 2.13/0.63  % (27080)Refutation found. Thanks to Tanya!
% 2.13/0.63  % SZS status Theorem for theBenchmark
% 2.13/0.63  % SZS output start Proof for theBenchmark
% 2.13/0.63  fof(f3269,plain,(
% 2.13/0.63    $false),
% 2.13/0.63    inference(avatar_sat_refutation,[],[f86,f91,f96,f110,f115,f138,f160,f167,f190,f221,f232,f272,f285,f339,f468,f473,f626,f667,f674,f757,f758,f990,f1016,f1179,f1185,f1219,f1253,f1359,f1387,f1404,f1541,f1981,f2094,f2138,f2139,f2493,f2745,f2963,f2985,f3268])).
% 2.13/0.63  fof(f3268,plain,(
% 2.13/0.63    ~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46 | ~spl4_54 | ~spl4_56 | ~spl4_121),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f3267])).
% 2.13/0.63  fof(f3267,plain,(
% 2.13/0.63    $false | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46 | ~spl4_54 | ~spl4_56 | ~spl4_121)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2998,f933])).
% 2.13/0.63  fof(f933,plain,(
% 2.13/0.63    v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~spl4_54),
% 2.13/0.63    inference(avatar_component_clause,[],[f932])).
% 2.13/0.63  fof(f932,plain,(
% 2.13/0.63    spl4_54 <=> v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 2.13/0.63  fof(f2998,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46 | ~spl4_56 | ~spl4_121)),
% 2.13/0.63    inference(forward_demodulation,[],[f2997,f324])).
% 2.13/0.63  fof(f324,plain,(
% 2.13/0.63    k1_xboole_0 = k2_struct_0(sK0) | ~spl4_19),
% 2.13/0.63    inference(avatar_component_clause,[],[f322])).
% 2.13/0.63  fof(f322,plain,(
% 2.13/0.63    spl4_19 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.13/0.63  fof(f2997,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46 | ~spl4_56 | ~spl4_121)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2996,f2744])).
% 2.13/0.63  fof(f2744,plain,(
% 2.13/0.63    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl4_121),
% 2.13/0.63    inference(avatar_component_clause,[],[f2742])).
% 2.13/0.63  fof(f2742,plain,(
% 2.13/0.63    spl4_121 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_121])])).
% 2.13/0.63  fof(f2996,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46 | ~spl4_56)),
% 2.13/0.63    inference(forward_demodulation,[],[f2995,f324])).
% 2.13/0.63  fof(f2995,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46 | ~spl4_56)),
% 2.13/0.63    inference(forward_demodulation,[],[f2994,f231])).
% 2.13/0.63  fof(f231,plain,(
% 2.13/0.63    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) | ~spl4_15),
% 2.13/0.63    inference(avatar_component_clause,[],[f229])).
% 2.13/0.63  fof(f229,plain,(
% 2.13/0.63    spl4_15 <=> u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.13/0.63  fof(f2994,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46 | ~spl4_56)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2993,f1177])).
% 2.13/0.63  fof(f1177,plain,(
% 2.13/0.63    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~spl4_56),
% 2.13/0.63    inference(avatar_component_clause,[],[f1175])).
% 2.13/0.63  fof(f1175,plain,(
% 2.13/0.63    spl4_56 <=> v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 2.13/0.63  fof(f2993,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(forward_demodulation,[],[f2992,f324])).
% 2.13/0.63  fof(f2992,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(forward_demodulation,[],[f2991,f231])).
% 2.13/0.63  fof(f2991,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_19 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2990,f205])).
% 2.13/0.63  fof(f205,plain,(
% 2.13/0.63    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~spl4_13),
% 2.13/0.63    inference(avatar_component_clause,[],[f203])).
% 2.13/0.63  fof(f203,plain,(
% 2.13/0.63    spl4_13 <=> v1_funct_1(k6_partfun1(k2_struct_0(sK0)))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.13/0.63  fof(f2990,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_19 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2701,f634])).
% 2.13/0.63  fof(f634,plain,(
% 2.13/0.63    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl4_41),
% 2.13/0.63    inference(avatar_component_clause,[],[f633])).
% 2.13/0.63  fof(f633,plain,(
% 2.13/0.63    spl4_41 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.13/0.63  fof(f2701,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_8 | ~spl4_19 | spl4_46)),
% 2.13/0.63    inference(resolution,[],[f2419,f729])).
% 2.13/0.63  fof(f729,plain,(
% 2.13/0.63    ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0) | spl4_46),
% 2.13/0.63    inference(avatar_component_clause,[],[f727])).
% 2.13/0.63  fof(f727,plain,(
% 2.13/0.63    spl4_46 <=> sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.13/0.63  fof(f2419,plain,(
% 2.13/0.63    ( ! [X61,X60] : (sP2(X61,X60,sK0) | ~v1_funct_2(X61,k1_xboole_0,u1_struct_0(X60)) | ~l1_pre_topc(X60) | ~v1_funct_1(X61) | ~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X60)))) | ~v5_pre_topc(X61,sK0,X60)) ) | (~spl4_3 | ~spl4_8 | ~spl4_19)),
% 2.13/0.63    inference(forward_demodulation,[],[f2418,f324])).
% 2.13/0.63  fof(f2418,plain,(
% 2.13/0.63    ( ! [X61,X60] : (~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X60)))) | ~v1_funct_2(X61,k1_xboole_0,u1_struct_0(X60)) | ~l1_pre_topc(X60) | ~v1_funct_1(X61) | sP2(X61,X60,sK0) | ~v5_pre_topc(X61,sK0,X60)) ) | (~spl4_3 | ~spl4_8 | ~spl4_19)),
% 2.13/0.63    inference(forward_demodulation,[],[f2417,f137])).
% 2.13/0.63  fof(f137,plain,(
% 2.13/0.63    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_8),
% 2.13/0.63    inference(avatar_component_clause,[],[f135])).
% 2.13/0.63  fof(f135,plain,(
% 2.13/0.63    spl4_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.13/0.63  fof(f2417,plain,(
% 2.13/0.63    ( ! [X61,X60] : (~v1_funct_2(X61,k1_xboole_0,u1_struct_0(X60)) | ~l1_pre_topc(X60) | ~v1_funct_1(X61) | ~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60)))) | sP2(X61,X60,sK0) | ~v5_pre_topc(X61,sK0,X60)) ) | (~spl4_3 | ~spl4_8 | ~spl4_19)),
% 2.13/0.63    inference(forward_demodulation,[],[f2416,f324])).
% 2.13/0.63  fof(f2416,plain,(
% 2.13/0.63    ( ! [X61,X60] : (~v1_funct_2(X61,k2_struct_0(sK0),u1_struct_0(X60)) | ~l1_pre_topc(X60) | ~v1_funct_1(X61) | ~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60)))) | sP2(X61,X60,sK0) | ~v5_pre_topc(X61,sK0,X60)) ) | (~spl4_3 | ~spl4_8 | ~spl4_19)),
% 2.13/0.63    inference(forward_demodulation,[],[f2415,f137])).
% 2.13/0.63  fof(f2415,plain,(
% 2.13/0.63    ( ! [X61,X60] : (~l1_pre_topc(X60) | ~v1_funct_1(X61) | ~v1_funct_2(X61,u1_struct_0(sK0),u1_struct_0(X60)) | ~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60)))) | sP2(X61,X60,sK0) | ~v5_pre_topc(X61,sK0,X60)) ) | (~spl4_3 | ~spl4_19)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2406,f95])).
% 2.13/0.63  fof(f95,plain,(
% 2.13/0.63    l1_pre_topc(sK0) | ~spl4_3),
% 2.13/0.63    inference(avatar_component_clause,[],[f93])).
% 2.13/0.63  fof(f93,plain,(
% 2.13/0.63    spl4_3 <=> l1_pre_topc(sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.13/0.63  fof(f2406,plain,(
% 2.13/0.63    ( ! [X61,X60] : (~l1_pre_topc(X60) | ~v1_funct_1(X61) | ~v1_funct_2(X61,u1_struct_0(sK0),u1_struct_0(X60)) | ~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60)))) | ~l1_pre_topc(sK0) | sP2(X61,X60,sK0) | ~v5_pre_topc(X61,sK0,X60)) ) | ~spl4_19),
% 2.13/0.63    inference(trivial_inequality_removal,[],[f2403])).
% 2.13/0.63  fof(f2403,plain,(
% 2.13/0.63    ( ! [X61,X60] : (k1_xboole_0 != k1_xboole_0 | ~l1_pre_topc(X60) | ~v1_funct_1(X61) | ~v1_funct_2(X61,u1_struct_0(sK0),u1_struct_0(X60)) | ~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X60)))) | ~l1_pre_topc(sK0) | sP2(X61,X60,sK0) | ~v5_pre_topc(X61,sK0,X60)) ) | ~spl4_19),
% 2.13/0.63    inference(superposition,[],[f58,f324])).
% 2.13/0.63  fof(f58,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | sP2(X2,X1,X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f23,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(flattening,[],[f22])).
% 2.13/0.63  fof(f22,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(ennf_transformation,[],[f7])).
% 2.13/0.63  fof(f7,axiom,(
% 2.13/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 2.13/0.63  fof(f2985,plain,(
% 2.13/0.63    k1_xboole_0 != k2_struct_0(sK0) | sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.13/0.63  fof(f2963,plain,(
% 2.13/0.63    ~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | ~spl4_56 | spl4_60 | ~spl4_99 | ~spl4_121),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f2962])).
% 2.13/0.63  fof(f2962,plain,(
% 2.13/0.63    $false | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | ~spl4_56 | spl4_60 | ~spl4_99 | ~spl4_121)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2961,f1177])).
% 2.13/0.63  fof(f2961,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60 | ~spl4_99 | ~spl4_121)),
% 2.13/0.63    inference(forward_demodulation,[],[f2960,f324])).
% 2.13/0.63  fof(f2960,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k2_struct_0(sK0)) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60 | ~spl4_99 | ~spl4_121)),
% 2.13/0.63    inference(forward_demodulation,[],[f2959,f231])).
% 2.13/0.63  fof(f2959,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60 | ~spl4_99 | ~spl4_121)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2958,f2047])).
% 2.13/0.63  fof(f2047,plain,(
% 2.13/0.63    sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~spl4_99),
% 2.13/0.63    inference(avatar_component_clause,[],[f2046])).
% 2.13/0.63  fof(f2046,plain,(
% 2.13/0.63    spl4_99 <=> sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 2.13/0.63  fof(f2958,plain,(
% 2.13/0.63    ~sP2(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60 | ~spl4_121)),
% 2.13/0.63    inference(forward_demodulation,[],[f2957,f324])).
% 2.13/0.63  fof(f2957,plain,(
% 2.13/0.63    ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60 | ~spl4_121)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2956,f2744])).
% 2.13/0.63  fof(f2956,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(forward_demodulation,[],[f2955,f324])).
% 2.13/0.63  fof(f2955,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(forward_demodulation,[],[f2954,f231])).
% 2.13/0.63  fof(f2954,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_13 | ~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2953,f205])).
% 2.13/0.63  fof(f2953,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2950,f634])).
% 2.13/0.63  fof(f2950,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | (~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(resolution,[],[f2948,f1358])).
% 2.13/0.63  fof(f1358,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | spl4_60),
% 2.13/0.63    inference(avatar_component_clause,[],[f1356])).
% 2.13/0.63  fof(f1356,plain,(
% 2.13/0.63    spl4_60 <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 2.13/0.63  fof(f2948,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~sP2(X1,X0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X1,k1_xboole_0,u1_struct_0(X0))) ) | (~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41)),
% 2.13/0.63    inference(forward_demodulation,[],[f2947,f324])).
% 2.13/0.63  fof(f2947,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~sP2(X1,X0,k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0)) ) | (~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41)),
% 2.13/0.63    inference(forward_demodulation,[],[f2946,f324])).
% 2.13/0.63  fof(f2946,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~sP2(X1,X0,k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0)) ) | (~spl4_15 | ~spl4_19 | ~spl4_30 | ~spl4_41)),
% 2.13/0.63    inference(subsumption_resolution,[],[f775,f324])).
% 2.13/0.63  fof(f775,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~sP2(X1,X0,k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0)) ) | (~spl4_15 | ~spl4_30 | ~spl4_41)),
% 2.13/0.63    inference(subsumption_resolution,[],[f521,f634])).
% 2.13/0.63  fof(f521,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~sP2(X1,X0,k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0)) ) | (~spl4_15 | ~spl4_30)),
% 2.13/0.63    inference(forward_demodulation,[],[f520,f231])).
% 2.13/0.63  fof(f520,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~sP2(X1,X0,k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0)) ) | (~spl4_15 | ~spl4_30)),
% 2.13/0.63    inference(forward_demodulation,[],[f469,f231])).
% 2.13/0.63  fof(f469,plain,(
% 2.13/0.63    ( ! [X0,X1] : (k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~sP2(X1,X0,k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),X0)) ) | ~spl4_30),
% 2.13/0.63    inference(superposition,[],[f57,f467])).
% 2.13/0.63  fof(f467,plain,(
% 2.13/0.63    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~spl4_30),
% 2.13/0.63    inference(avatar_component_clause,[],[f465])).
% 2.13/0.63  fof(f465,plain,(
% 2.13/0.63    spl4_30 <=> k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.13/0.63  fof(f57,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (k2_struct_0(X0) != k1_xboole_0 | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | ~sP2(X2,X1,X0) | v5_pre_topc(X2,X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f2745,plain,(
% 2.13/0.63    spl4_121 | ~spl4_19 | ~spl4_28),
% 2.13/0.63    inference(avatar_split_clause,[],[f2327,f454,f322,f2742])).
% 2.13/0.63  fof(f454,plain,(
% 2.13/0.63    spl4_28 <=> m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.13/0.63  fof(f2327,plain,(
% 2.13/0.63    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_19 | ~spl4_28)),
% 2.13/0.63    inference(superposition,[],[f455,f324])).
% 2.13/0.63  fof(f455,plain,(
% 2.13/0.63    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~spl4_28),
% 2.13/0.63    inference(avatar_component_clause,[],[f454])).
% 2.13/0.63  fof(f2493,plain,(
% 2.13/0.63    spl4_56 | ~spl4_19 | ~spl4_58),
% 2.13/0.63    inference(avatar_split_clause,[],[f2492,f1214,f322,f1175])).
% 2.13/0.63  fof(f1214,plain,(
% 2.13/0.63    spl4_58 <=> v1_funct_2(k6_partfun1(k1_xboole_0),k2_struct_0(sK0),k2_struct_0(sK0))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.13/0.63  fof(f2492,plain,(
% 2.13/0.63    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl4_19 | ~spl4_58)),
% 2.13/0.63    inference(forward_demodulation,[],[f1215,f324])).
% 2.13/0.63  fof(f1215,plain,(
% 2.13/0.63    v1_funct_2(k6_partfun1(k1_xboole_0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl4_58),
% 2.13/0.63    inference(avatar_component_clause,[],[f1214])).
% 2.13/0.63  fof(f2139,plain,(
% 2.13/0.63    sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) != k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.13/0.63  fof(f2138,plain,(
% 2.13/0.63    spl4_105 | ~spl4_28 | ~spl4_91),
% 2.13/0.63    inference(avatar_split_clause,[],[f1997,f1978,f454,f2135])).
% 2.13/0.63  fof(f2135,plain,(
% 2.13/0.63    spl4_105 <=> sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_105])])).
% 2.13/0.63  fof(f1978,plain,(
% 2.13/0.63    spl4_91 <=> sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 2.13/0.63  fof(f1997,plain,(
% 2.13/0.63    sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | (~spl4_28 | ~spl4_91)),
% 2.13/0.63    inference(superposition,[],[f1980,f481])).
% 2.13/0.63  fof(f481,plain,(
% 2.13/0.63    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)) ) | ~spl4_28),
% 2.13/0.63    inference(resolution,[],[f455,f76])).
% 2.13/0.63  fof(f76,plain,(
% 2.13/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f39])).
% 2.13/0.63  fof(f39,plain,(
% 2.13/0.63    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.13/0.63    inference(ennf_transformation,[],[f1])).
% 2.13/0.63  fof(f1,axiom,(
% 2.13/0.63    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 2.13/0.63  fof(f1980,plain,(
% 2.13/0.63    sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | ~spl4_91),
% 2.13/0.63    inference(avatar_component_clause,[],[f1978])).
% 2.13/0.63  fof(f2094,plain,(
% 2.13/0.63    spl4_61 | spl4_103),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f2093])).
% 2.13/0.63  fof(f2093,plain,(
% 2.13/0.63    $false | (spl4_61 | spl4_103)),
% 2.13/0.63    inference(subsumption_resolution,[],[f2092,f1386])).
% 2.13/0.63  fof(f1386,plain,(
% 2.13/0.63    ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | spl4_61),
% 2.13/0.63    inference(avatar_component_clause,[],[f1384])).
% 2.13/0.63  fof(f1384,plain,(
% 2.13/0.63    spl4_61 <=> sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 2.13/0.63  fof(f2092,plain,(
% 2.13/0.63    sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | spl4_103),
% 2.13/0.63    inference(resolution,[],[f2090,f54])).
% 2.13/0.63  fof(f54,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (v3_pre_topc(sK3(X0,X1,X2),X1) | sP2(X2,X1,X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f2090,plain,(
% 2.13/0.63    ~v3_pre_topc(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | spl4_103),
% 2.13/0.63    inference(avatar_component_clause,[],[f2088])).
% 2.13/0.63  fof(f2088,plain,(
% 2.13/0.63    spl4_103 <=> v3_pre_topc(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).
% 2.13/0.63  fof(f1981,plain,(
% 2.13/0.63    spl4_91 | ~spl4_62),
% 2.13/0.63    inference(avatar_split_clause,[],[f1415,f1401,f1978])).
% 2.13/0.63  fof(f1401,plain,(
% 2.13/0.63    spl4_62 <=> m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 2.13/0.63  fof(f1415,plain,(
% 2.13/0.63    sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | ~spl4_62),
% 2.13/0.63    inference(resolution,[],[f1403,f69])).
% 2.13/0.63  fof(f69,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1) )),
% 2.13/0.63    inference(cnf_transformation,[],[f34])).
% 2.13/0.63  fof(f34,plain,(
% 2.13/0.63    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f2])).
% 2.13/0.63  fof(f2,axiom,(
% 2.13/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 2.13/0.63  fof(f1403,plain,(
% 2.13/0.63    m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_62),
% 2.13/0.63    inference(avatar_component_clause,[],[f1401])).
% 2.13/0.63  fof(f1541,plain,(
% 2.13/0.63    ~spl4_69 | ~spl4_15 | ~spl4_28 | spl4_61),
% 2.13/0.63    inference(avatar_split_clause,[],[f1396,f1384,f454,f229,f1538])).
% 2.13/0.63  fof(f1538,plain,(
% 2.13/0.63    spl4_69 <=> v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 2.13/0.63  fof(f1396,plain,(
% 2.13/0.63    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | (~spl4_15 | ~spl4_28 | spl4_61)),
% 2.13/0.63    inference(forward_demodulation,[],[f1395,f481])).
% 2.13/0.63  fof(f1395,plain,(
% 2.13/0.63    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | (~spl4_15 | spl4_61)),
% 2.13/0.63    inference(forward_demodulation,[],[f1391,f231])).
% 2.13/0.63  fof(f1391,plain,(
% 2.13/0.63    ~v3_pre_topc(k8_relset_1(u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | (~spl4_15 | spl4_61)),
% 2.13/0.63    inference(resolution,[],[f1386,f241])).
% 2.13/0.63  fof(f241,plain,(
% 2.13/0.63    ( ! [X4,X3] : (sP2(X4,k6_tmap_1(sK0,sK1),X3) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X3),k2_struct_0(sK0),X4,sK3(X3,k6_tmap_1(sK0,sK1),X4)),X3)) ) | ~spl4_15),
% 2.13/0.63    inference(superposition,[],[f55,f231])).
% 2.13/0.63  fof(f55,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) | sP2(X2,X1,X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f1404,plain,(
% 2.13/0.63    spl4_62 | ~spl4_15 | spl4_61),
% 2.13/0.63    inference(avatar_split_clause,[],[f1399,f1384,f229,f1401])).
% 2.13/0.63  fof(f1399,plain,(
% 2.13/0.63    m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_15 | spl4_61)),
% 2.13/0.63    inference(forward_demodulation,[],[f1393,f231])).
% 2.13/0.63  fof(f1393,plain,(
% 2.13/0.63    m1_subset_1(sK3(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | spl4_61),
% 2.13/0.63    inference(resolution,[],[f1386,f53])).
% 2.13/0.63  fof(f53,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f1387,plain,(
% 2.13/0.63    ~spl4_61 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_28 | spl4_36 | ~spl4_41 | spl4_60),
% 2.13/0.63    inference(avatar_split_clause,[],[f1381,f1356,f633,f512,f454,f282,f229,f203,f1384])).
% 2.13/0.63  fof(f282,plain,(
% 2.13/0.63    spl4_18 <=> v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.13/0.63  fof(f512,plain,(
% 2.13/0.63    spl4_36 <=> k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.13/0.63  fof(f1381,plain,(
% 2.13/0.63    ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_28 | spl4_36 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1380,f455])).
% 2.13/0.63  fof(f1380,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_13 | ~spl4_15 | ~spl4_18 | spl4_36 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(forward_demodulation,[],[f1379,f231])).
% 2.13/0.63  fof(f1379,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_13 | ~spl4_15 | ~spl4_18 | spl4_36 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1378,f284])).
% 2.13/0.63  fof(f284,plain,(
% 2.13/0.63    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl4_18),
% 2.13/0.63    inference(avatar_component_clause,[],[f282])).
% 2.13/0.63  fof(f1378,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_13 | ~spl4_15 | spl4_36 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(forward_demodulation,[],[f1377,f231])).
% 2.13/0.63  fof(f1377,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_13 | spl4_36 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1376,f513])).
% 2.13/0.63  fof(f513,plain,(
% 2.13/0.63    k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | spl4_36),
% 2.13/0.63    inference(avatar_component_clause,[],[f512])).
% 2.13/0.63  fof(f1376,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_13 | ~spl4_41 | spl4_60)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1362,f634])).
% 2.13/0.63  fof(f1362,plain,(
% 2.13/0.63    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_13 | spl4_60)),
% 2.13/0.63    inference(duplicate_literal_removal,[],[f1361])).
% 2.13/0.63  fof(f1361,plain,(
% 2.13/0.63    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl4_13 | spl4_60)),
% 2.13/0.63    inference(resolution,[],[f1358,f443])).
% 2.13/0.63  fof(f443,plain,(
% 2.13/0.63    ( ! [X4,X5] : (v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),X5,X4) | ~l1_pre_topc(X5) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(X5),u1_struct_0(X4)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X4)))) | k1_xboole_0 = k2_struct_0(X4) | ~sP2(k6_partfun1(k2_struct_0(sK0)),X4,X5) | ~l1_pre_topc(X4)) ) | ~spl4_13),
% 2.13/0.63    inference(resolution,[],[f205,f59])).
% 2.13/0.63  fof(f59,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | ~sP2(X2,X1,X0) | v5_pre_topc(X2,X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f1359,plain,(
% 2.13/0.63    ~spl4_60 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42),
% 2.13/0.63    inference(avatar_split_clause,[],[f1350,f637,f633,f454,f282,f269,f229,f218,f203,f135,f93,f88,f1356])).
% 2.13/0.63  fof(f88,plain,(
% 2.13/0.63    spl4_2 <=> v2_pre_topc(sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.13/0.63  fof(f218,plain,(
% 2.13/0.63    spl4_14 <=> v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.13/0.63  fof(f269,plain,(
% 2.13/0.63    spl4_17 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.13/0.63  fof(f637,plain,(
% 2.13/0.63    spl4_42 <=> v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 2.13/0.63  fof(f1350,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1349,f271])).
% 2.13/0.63  fof(f271,plain,(
% 2.13/0.63    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~spl4_17),
% 2.13/0.63    inference(avatar_component_clause,[],[f269])).
% 2.13/0.63  fof(f1349,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1348,f137])).
% 2.13/0.63  fof(f1348,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1347,f455])).
% 2.13/0.63  fof(f1347,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1346,f231])).
% 2.13/0.63  fof(f1346,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1345,f271])).
% 2.13/0.63  fof(f1345,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1344,f137])).
% 2.13/0.63  fof(f1344,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1343,f231])).
% 2.13/0.63  fof(f1343,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1342,f284])).
% 2.13/0.63  fof(f1342,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1341,f231])).
% 2.13/0.63  fof(f1341,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1340,f271])).
% 2.13/0.63  fof(f1340,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1339,f137])).
% 2.13/0.63  fof(f1339,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1338,f231])).
% 2.13/0.63  fof(f1338,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_28 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1337,f455])).
% 2.13/0.63  fof(f1337,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1336,f137])).
% 2.13/0.63  fof(f1336,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1335,f231])).
% 2.13/0.63  fof(f1335,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1334,f284])).
% 2.13/0.63  fof(f1334,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1333,f137])).
% 2.13/0.63  fof(f1333,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_13 | spl4_14 | ~spl4_15 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(forward_demodulation,[],[f1332,f231])).
% 2.13/0.63  fof(f1332,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_13 | spl4_14 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1331,f95])).
% 2.13/0.63  fof(f1331,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl4_2 | ~spl4_13 | spl4_14 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1330,f90])).
% 2.13/0.63  fof(f90,plain,(
% 2.13/0.63    v2_pre_topc(sK0) | ~spl4_2),
% 2.13/0.63    inference(avatar_component_clause,[],[f88])).
% 2.13/0.63  fof(f1330,plain,(
% 2.13/0.63    ~v2_pre_topc(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl4_13 | spl4_14 | ~spl4_41 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1329,f634])).
% 2.13/0.63  fof(f1329,plain,(
% 2.13/0.63    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl4_13 | spl4_14 | ~spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1328,f638])).
% 2.13/0.63  fof(f638,plain,(
% 2.13/0.63    v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl4_42),
% 2.13/0.63    inference(avatar_component_clause,[],[f637])).
% 2.13/0.63  fof(f1328,plain,(
% 2.13/0.63    ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | (~spl4_13 | spl4_14)),
% 2.13/0.63    inference(resolution,[],[f441,f220])).
% 2.13/0.63  fof(f220,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | spl4_14),
% 2.13/0.63    inference(avatar_component_clause,[],[f218])).
% 2.13/0.63  fof(f441,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),X0,X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0)) ) | ~spl4_13),
% 2.13/0.63    inference(resolution,[],[f205,f81])).
% 2.13/0.63  fof(f81,plain,(
% 2.13/0.63    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.13/0.63    inference(duplicate_literal_removal,[],[f79])).
% 2.13/0.63  fof(f79,plain,(
% 2.13/0.63    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.13/0.63    inference(equality_resolution,[],[f67])).
% 2.13/0.63  fof(f67,plain,(
% 2.13/0.63    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f33])).
% 2.13/0.63  fof(f33,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.13/0.63    inference(flattening,[],[f32])).
% 2.13/0.63  fof(f32,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f5])).
% 2.13/0.63  fof(f5,axiom,(
% 2.13/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.13/0.63  fof(f1253,plain,(
% 2.13/0.63    ~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_28 | spl4_36 | ~spl4_41 | spl4_46),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f1252])).
% 2.13/0.63  fof(f1252,plain,(
% 2.13/0.63    $false | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_28 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1251,f455])).
% 2.13/0.63  fof(f1251,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_18 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(forward_demodulation,[],[f1250,f137])).
% 2.13/0.63  fof(f1250,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_18 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(forward_demodulation,[],[f1249,f231])).
% 2.13/0.63  fof(f1249,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_18 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1248,f284])).
% 2.13/0.63  fof(f1248,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_3 | ~spl4_8 | ~spl4_13 | ~spl4_14 | ~spl4_15 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(forward_demodulation,[],[f1247,f137])).
% 2.13/0.63  fof(f1247,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_15 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(forward_demodulation,[],[f1246,f231])).
% 2.13/0.63  fof(f1246,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_3 | ~spl4_13 | ~spl4_14 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1245,f219])).
% 2.13/0.63  fof(f219,plain,(
% 2.13/0.63    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~spl4_14),
% 2.13/0.63    inference(avatar_component_clause,[],[f218])).
% 2.13/0.63  fof(f1245,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_13 | spl4_36 | ~spl4_41 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1244,f634])).
% 2.13/0.63  fof(f1244,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_13 | spl4_36 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1243,f513])).
% 2.13/0.63  fof(f1243,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_13 | spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1239,f95])).
% 2.13/0.63  fof(f1239,plain,(
% 2.13/0.63    ~l1_pre_topc(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_13 | spl4_46)),
% 2.13/0.63    inference(resolution,[],[f729,f444])).
% 2.13/0.63  fof(f444,plain,(
% 2.13/0.63    ( ! [X6,X7] : (sP2(k6_partfun1(k2_struct_0(sK0)),X6,X7) | ~l1_pre_topc(X7) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(X7),u1_struct_0(X6)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X6)))) | k1_xboole_0 = k2_struct_0(X6) | ~l1_pre_topc(X6) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),X7,X6)) ) | ~spl4_13),
% 2.13/0.63    inference(resolution,[],[f205,f60])).
% 2.13/0.63  fof(f60,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | sP2(X2,X1,X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f1219,plain,(
% 2.13/0.63    k7_tmap_1(sK0,sK1) != k6_partfun1(k1_xboole_0) | k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0)) | v1_funct_2(k6_partfun1(k1_xboole_0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 2.13/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.13/0.63  fof(f1185,plain,(
% 2.13/0.63    spl4_14 | spl4_6 | ~spl4_12),
% 2.13/0.63    inference(avatar_split_clause,[],[f1183,f187,f119,f218])).
% 2.13/0.63  fof(f119,plain,(
% 2.13/0.63    spl4_6 <=> v3_pre_topc(sK1,sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.13/0.63  fof(f187,plain,(
% 2.13/0.63    spl4_12 <=> k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.13/0.63  fof(f1183,plain,(
% 2.13/0.63    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (spl4_6 | ~spl4_12)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1011,f120])).
% 2.13/0.63  fof(f120,plain,(
% 2.13/0.63    ~v3_pre_topc(sK1,sK0) | spl4_6),
% 2.13/0.63    inference(avatar_component_clause,[],[f119])).
% 2.13/0.63  fof(f1011,plain,(
% 2.13/0.63    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~spl4_12),
% 2.13/0.63    inference(forward_demodulation,[],[f43,f189])).
% 2.13/0.63  fof(f189,plain,(
% 2.13/0.63    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) | ~spl4_12),
% 2.13/0.63    inference(avatar_component_clause,[],[f187])).
% 2.13/0.63  fof(f43,plain,(
% 2.13/0.63    v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.13/0.63    inference(cnf_transformation,[],[f17])).
% 2.13/0.63  fof(f17,plain,(
% 2.13/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/0.63    inference(flattening,[],[f16])).
% 2.13/0.63  fof(f16,plain,(
% 2.13/0.63    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f15])).
% 2.13/0.63  fof(f15,negated_conjecture,(
% 2.13/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.13/0.63    inference(negated_conjecture,[],[f14])).
% 2.13/0.63  fof(f14,conjecture,(
% 2.13/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).
% 2.13/0.63  fof(f1179,plain,(
% 2.13/0.63    k7_tmap_1(sK0,sK1) != k6_partfun1(k1_xboole_0) | k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.13/0.63  fof(f1016,plain,(
% 2.13/0.63    spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_39 | ~spl4_46),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f1015])).
% 2.13/0.63  fof(f1015,plain,(
% 2.13/0.63    $false | (spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_39 | ~spl4_46)),
% 2.13/0.63    inference(subsumption_resolution,[],[f1014,f728])).
% 2.13/0.63  fof(f728,plain,(
% 2.13/0.63    sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0) | ~spl4_46),
% 2.13/0.63    inference(avatar_component_clause,[],[f727])).
% 2.13/0.63  fof(f1014,plain,(
% 2.13/0.63    ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0) | (spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_39)),
% 2.13/0.63    inference(subsumption_resolution,[],[f698,f120])).
% 2.13/0.63  fof(f698,plain,(
% 2.13/0.63    v3_pre_topc(sK1,sK0) | ~sP2(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),sK0) | (~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_15 | ~spl4_39)),
% 2.13/0.63    inference(superposition,[],[f696,f166])).
% 2.13/0.63  fof(f166,plain,(
% 2.13/0.63    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) | ~spl4_11),
% 2.13/0.63    inference(avatar_component_clause,[],[f164])).
% 2.13/0.63  fof(f164,plain,(
% 2.13/0.63    spl4_11 <=> sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.13/0.63  fof(f696,plain,(
% 2.13/0.63    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0,sK1),sK0) | ~sP2(X0,k6_tmap_1(sK0,sK1),sK0)) ) | (~spl4_8 | ~spl4_10 | ~spl4_15 | ~spl4_39)),
% 2.13/0.63    inference(superposition,[],[f695,f137])).
% 2.13/0.63  fof(f695,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK0),X1,sK1),X0) | ~sP2(X1,k6_tmap_1(sK0,sK1),X0)) ) | (~spl4_10 | ~spl4_15 | ~spl4_39)),
% 2.13/0.63    inference(subsumption_resolution,[],[f627,f620])).
% 2.13/0.63  fof(f620,plain,(
% 2.13/0.63    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | ~spl4_39),
% 2.13/0.63    inference(avatar_component_clause,[],[f618])).
% 2.13/0.63  fof(f618,plain,(
% 2.13/0.63    spl4_39 <=> v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.13/0.63  fof(f627,plain,(
% 2.13/0.63    ( ! [X0,X1] : (~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),k2_struct_0(sK0),X1,sK1),X0) | ~sP2(X1,k6_tmap_1(sK0,sK1),X0)) ) | (~spl4_10 | ~spl4_15)),
% 2.13/0.63    inference(resolution,[],[f243,f159])).
% 2.13/0.63  fof(f159,plain,(
% 2.13/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl4_10),
% 2.13/0.63    inference(avatar_component_clause,[],[f157])).
% 2.13/0.63  fof(f157,plain,(
% 2.13/0.63    spl4_10 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.13/0.63  fof(f243,plain,(
% 2.13/0.63    ( ! [X8,X7,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X7,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(X8),k2_struct_0(sK0),X9,X7),X8) | ~sP2(X9,k6_tmap_1(sK0,sK1),X8)) ) | ~spl4_15),
% 2.13/0.63    inference(superposition,[],[f56,f231])).
% 2.13/0.63  fof(f56,plain,(
% 2.13/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~sP2(X2,X1,X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f23])).
% 2.13/0.63  fof(f990,plain,(
% 2.13/0.63    ~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_28),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f989])).
% 2.13/0.63  fof(f989,plain,(
% 2.13/0.63    $false | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f986,f219])).
% 2.13/0.63  fof(f986,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f985,f455])).
% 2.13/0.63  fof(f985,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18)),
% 2.13/0.63    inference(forward_demodulation,[],[f984,f189])).
% 2.13/0.63  fof(f984,plain,(
% 2.13/0.63    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18)),
% 2.13/0.63    inference(forward_demodulation,[],[f983,f137])).
% 2.13/0.63  fof(f983,plain,(
% 2.13/0.63    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18)),
% 2.13/0.63    inference(forward_demodulation,[],[f982,f231])).
% 2.13/0.63  fof(f982,plain,(
% 2.13/0.63    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18)),
% 2.13/0.63    inference(forward_demodulation,[],[f981,f189])).
% 2.13/0.63  fof(f981,plain,(
% 2.13/0.63    ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18)),
% 2.13/0.63    inference(subsumption_resolution,[],[f980,f284])).
% 2.13/0.63  fof(f980,plain,(
% 2.13/0.63    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f979,f189])).
% 2.13/0.63  fof(f979,plain,(
% 2.13/0.63    ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_6 | ~spl4_8 | ~spl4_12 | ~spl4_13 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f978,f137])).
% 2.13/0.63  fof(f978,plain,(
% 2.13/0.63    ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_6 | ~spl4_12 | ~spl4_13 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f977,f231])).
% 2.13/0.63  fof(f977,plain,(
% 2.13/0.63    ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_6 | ~spl4_12 | ~spl4_13)),
% 2.13/0.63    inference(subsumption_resolution,[],[f976,f205])).
% 2.13/0.63  fof(f976,plain,(
% 2.13/0.63    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (~spl4_6 | ~spl4_12)),
% 2.13/0.63    inference(forward_demodulation,[],[f975,f189])).
% 2.13/0.63  fof(f975,plain,(
% 2.13/0.63    ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~spl4_6),
% 2.13/0.63    inference(subsumption_resolution,[],[f40,f121])).
% 2.13/0.63  fof(f121,plain,(
% 2.13/0.63    v3_pre_topc(sK1,sK0) | ~spl4_6),
% 2.13/0.63    inference(avatar_component_clause,[],[f119])).
% 2.13/0.63  fof(f40,plain,(
% 2.13/0.63    ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(sK1,sK0)),
% 2.13/0.63    inference(cnf_transformation,[],[f17])).
% 2.13/0.63  fof(f758,plain,(
% 2.13/0.63    k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | k2_struct_0(sK0) != k2_struct_0(k6_tmap_1(sK0,sK1)) | k7_tmap_1(sK0,sK1) != k6_partfun1(k2_struct_0(sK0)) | k7_tmap_1(sK0,sK1) = k6_partfun1(k1_xboole_0)),
% 2.13/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.13/0.63  fof(f757,plain,(
% 2.13/0.63    k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | k2_struct_0(sK0) != k2_struct_0(k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 2.13/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.13/0.63  fof(f674,plain,(
% 2.13/0.63    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_42),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f673])).
% 2.13/0.63  fof(f673,plain,(
% 2.13/0.63    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f672,f85])).
% 2.13/0.63  fof(f85,plain,(
% 2.13/0.63    ~v2_struct_0(sK0) | spl4_1),
% 2.13/0.63    inference(avatar_component_clause,[],[f83])).
% 2.13/0.63  fof(f83,plain,(
% 2.13/0.63    spl4_1 <=> v2_struct_0(sK0)),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.13/0.63  fof(f672,plain,(
% 2.13/0.63    v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f671,f109])).
% 2.13/0.63  fof(f109,plain,(
% 2.13/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 2.13/0.63    inference(avatar_component_clause,[],[f107])).
% 2.13/0.63  fof(f107,plain,(
% 2.13/0.63    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.13/0.63  fof(f671,plain,(
% 2.13/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f670,f95])).
% 2.13/0.63  fof(f670,plain,(
% 2.13/0.63    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_2 | spl4_42)),
% 2.13/0.63    inference(subsumption_resolution,[],[f669,f90])).
% 2.13/0.63  fof(f669,plain,(
% 2.13/0.63    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | spl4_42),
% 2.13/0.63    inference(resolution,[],[f639,f71])).
% 2.13/0.63  fof(f71,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f36])).
% 2.13/0.63  fof(f36,plain,(
% 2.13/0.63    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.63    inference(flattening,[],[f35])).
% 2.13/0.63  fof(f35,plain,(
% 2.13/0.63    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f9])).
% 2.13/0.63  fof(f9,axiom,(
% 2.13/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 2.13/0.63  fof(f639,plain,(
% 2.13/0.63    ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | spl4_42),
% 2.13/0.63    inference(avatar_component_clause,[],[f637])).
% 2.13/0.63  fof(f667,plain,(
% 2.13/0.63    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | spl4_41),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f666])).
% 2.13/0.63  fof(f666,plain,(
% 2.13/0.63    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | spl4_41)),
% 2.13/0.63    inference(subsumption_resolution,[],[f665,f159])).
% 2.13/0.63  fof(f665,plain,(
% 2.13/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_41)),
% 2.13/0.63    inference(resolution,[],[f635,f170])).
% 2.13/0.63  fof(f170,plain,(
% 2.13/0.63    ( ! [X4] : (l1_pre_topc(k6_tmap_1(sK0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f169,f137])).
% 2.13/0.63  fof(f169,plain,(
% 2.13/0.63    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X4))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.13/0.63    inference(subsumption_resolution,[],[f168,f95])).
% 2.13/0.63  fof(f168,plain,(
% 2.13/0.63    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X4))) ) | (spl4_1 | ~spl4_2)),
% 2.13/0.63    inference(subsumption_resolution,[],[f101,f90])).
% 2.13/0.63  fof(f101,plain,(
% 2.13/0.63    ( ! [X4] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X4))) ) | spl4_1),
% 2.13/0.63    inference(resolution,[],[f85,f72])).
% 2.13/0.63  fof(f72,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f36])).
% 2.13/0.63  fof(f635,plain,(
% 2.13/0.63    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | spl4_41),
% 2.13/0.63    inference(avatar_component_clause,[],[f633])).
% 2.13/0.63  fof(f626,plain,(
% 2.13/0.63    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_15 | spl4_39),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f625])).
% 2.13/0.63  fof(f625,plain,(
% 2.13/0.63    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_15 | spl4_39)),
% 2.13/0.63    inference(subsumption_resolution,[],[f624,f159])).
% 2.13/0.63  fof(f624,plain,(
% 2.13/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_15 | spl4_39)),
% 2.13/0.63    inference(forward_demodulation,[],[f623,f231])).
% 2.13/0.63  fof(f623,plain,(
% 2.13/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | spl4_39)),
% 2.13/0.63    inference(subsumption_resolution,[],[f622,f159])).
% 2.13/0.63  fof(f622,plain,(
% 2.13/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | spl4_39)),
% 2.13/0.63    inference(resolution,[],[f619,f255])).
% 2.13/0.63  fof(f255,plain,(
% 2.13/0.63    ( ! [X7] : (v3_pre_topc(X7,k6_tmap_1(sK0,X7)) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f254,f137])).
% 2.13/0.63  fof(f254,plain,(
% 2.13/0.63    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7)))) | v3_pre_topc(X7,k6_tmap_1(sK0,X7))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.13/0.63    inference(subsumption_resolution,[],[f253,f95])).
% 2.13/0.63  fof(f253,plain,(
% 2.13/0.63    ( ! [X7] : (~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7)))) | v3_pre_topc(X7,k6_tmap_1(sK0,X7))) ) | (spl4_1 | ~spl4_2)),
% 2.13/0.63    inference(subsumption_resolution,[],[f104,f90])).
% 2.13/0.63  fof(f104,plain,(
% 2.13/0.63    ( ! [X7] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X7)))) | v3_pre_topc(X7,k6_tmap_1(sK0,X7))) ) | spl4_1),
% 2.13/0.63    inference(resolution,[],[f85,f77])).
% 2.13/0.63  fof(f77,plain,(
% 2.13/0.63    ( ! [X2,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | v3_pre_topc(X2,k6_tmap_1(X0,X2))) )),
% 2.13/0.63    inference(equality_resolution,[],[f66])).
% 2.13/0.63  fof(f66,plain,(
% 2.13/0.63    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | X1 != X2 | v3_pre_topc(X2,k6_tmap_1(X0,X1))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f31])).
% 2.13/0.63  fof(f31,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.63    inference(flattening,[],[f30])).
% 2.13/0.63  fof(f30,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f12])).
% 2.13/0.63  fof(f12,axiom,(
% 2.13/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).
% 2.13/0.63  fof(f619,plain,(
% 2.13/0.63    ~v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) | spl4_39),
% 2.13/0.63    inference(avatar_component_clause,[],[f618])).
% 2.13/0.63  fof(f473,plain,(
% 2.13/0.63    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_12 | ~spl4_15 | spl4_28),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f472])).
% 2.13/0.63  fof(f472,plain,(
% 2.13/0.63    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_12 | ~spl4_15 | spl4_28)),
% 2.13/0.63    inference(subsumption_resolution,[],[f252,f456])).
% 2.13/0.63  fof(f456,plain,(
% 2.13/0.63    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | spl4_28),
% 2.13/0.63    inference(avatar_component_clause,[],[f454])).
% 2.13/0.63  fof(f252,plain,(
% 2.13/0.63    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_12 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f251,f189])).
% 2.13/0.63  fof(f251,plain,(
% 2.13/0.63    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f250,f231])).
% 2.13/0.63  fof(f250,plain,(
% 2.13/0.63    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10)),
% 2.13/0.63    inference(resolution,[],[f236,f159])).
% 2.13/0.63  fof(f236,plain,(
% 2.13/0.63    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6)))))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f235,f137])).
% 2.13/0.63  fof(f235,plain,(
% 2.13/0.63    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6)))))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f234,f137])).
% 2.13/0.63  fof(f234,plain,(
% 2.13/0.63    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6)))))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.13/0.63    inference(subsumption_resolution,[],[f233,f95])).
% 2.13/0.63  fof(f233,plain,(
% 2.13/0.63    ( ! [X6] : (~l1_pre_topc(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6)))))) ) | (spl4_1 | ~spl4_2)),
% 2.13/0.63    inference(subsumption_resolution,[],[f103,f90])).
% 2.13/0.63  fof(f103,plain,(
% 2.13/0.63    ( ! [X6] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X6)))))) ) | spl4_1),
% 2.13/0.63    inference(resolution,[],[f85,f75])).
% 2.13/0.63  fof(f75,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f38])).
% 2.13/0.63  fof(f38,plain,(
% 2.13/0.63    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.63    inference(flattening,[],[f37])).
% 2.13/0.63  fof(f37,plain,(
% 2.13/0.63    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f10])).
% 2.13/0.63  fof(f10,axiom,(
% 2.13/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 2.13/0.63  fof(f468,plain,(
% 2.13/0.63    spl4_30 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_15),
% 2.13/0.63    inference(avatar_split_clause,[],[f334,f229,f157,f135,f93,f88,f83,f465])).
% 2.13/0.63  fof(f334,plain,(
% 2.13/0.63    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f333,f231])).
% 2.13/0.63  fof(f333,plain,(
% 2.13/0.63    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10)),
% 2.13/0.63    inference(resolution,[],[f180,f159])).
% 2.13/0.63  fof(f180,plain,(
% 2.13/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k6_tmap_1(sK0,X0)) = k2_struct_0(k6_tmap_1(sK0,X0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(resolution,[],[f171,f49])).
% 2.13/0.63  fof(f49,plain,(
% 2.13/0.63    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f18])).
% 2.13/0.63  fof(f18,plain,(
% 2.13/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.13/0.63    inference(ennf_transformation,[],[f3])).
% 2.13/0.63  fof(f3,axiom,(
% 2.13/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.13/0.63  fof(f171,plain,(
% 2.13/0.63    ( ! [X0] : (l1_struct_0(k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(resolution,[],[f170,f52])).
% 2.13/0.63  fof(f52,plain,(
% 2.13/0.63    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f21])).
% 2.13/0.63  fof(f21,plain,(
% 2.13/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.13/0.63    inference(ennf_transformation,[],[f4])).
% 2.13/0.63  fof(f4,axiom,(
% 2.13/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.13/0.63  fof(f339,plain,(
% 2.13/0.63    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_12 | spl4_13),
% 2.13/0.63    inference(avatar_contradiction_clause,[],[f338])).
% 2.13/0.63  fof(f338,plain,(
% 2.13/0.63    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_12 | spl4_13)),
% 2.13/0.63    inference(subsumption_resolution,[],[f330,f204])).
% 2.13/0.63  fof(f204,plain,(
% 2.13/0.63    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | spl4_13),
% 2.13/0.63    inference(avatar_component_clause,[],[f203])).
% 2.13/0.63  fof(f330,plain,(
% 2.13/0.63    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10 | ~spl4_12)),
% 2.13/0.63    inference(forward_demodulation,[],[f175,f189])).
% 2.13/0.63  fof(f175,plain,(
% 2.13/0.63    v1_funct_1(k7_tmap_1(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10)),
% 2.13/0.63    inference(resolution,[],[f174,f159])).
% 2.13/0.63  fof(f174,plain,(
% 2.13/0.63    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X5))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f173,f137])).
% 2.13/0.63  fof(f173,plain,(
% 2.13/0.63    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X5))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.13/0.63    inference(subsumption_resolution,[],[f172,f95])).
% 2.13/0.63  fof(f172,plain,(
% 2.13/0.63    ( ! [X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X5))) ) | (spl4_1 | ~spl4_2)),
% 2.13/0.63    inference(subsumption_resolution,[],[f102,f90])).
% 2.13/0.63  fof(f102,plain,(
% 2.13/0.63    ( ! [X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X5))) ) | spl4_1),
% 2.13/0.63    inference(resolution,[],[f85,f73])).
% 2.13/0.63  fof(f73,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f38])).
% 2.13/0.63  fof(f285,plain,(
% 2.13/0.63    spl4_18 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_12 | ~spl4_15),
% 2.13/0.63    inference(avatar_split_clause,[],[f249,f229,f187,f135,f107,f93,f88,f83,f282])).
% 2.13/0.63  fof(f249,plain,(
% 2.13/0.63    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f248,f189])).
% 2.13/0.63  fof(f248,plain,(
% 2.13/0.63    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_8 | ~spl4_15)),
% 2.13/0.63    inference(forward_demodulation,[],[f247,f137])).
% 2.13/0.63  fof(f247,plain,(
% 2.13/0.63    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_15)),
% 2.13/0.63    inference(subsumption_resolution,[],[f246,f85])).
% 2.13/0.63  fof(f246,plain,(
% 2.13/0.63    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0)) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_15)),
% 2.13/0.63    inference(subsumption_resolution,[],[f245,f109])).
% 2.13/0.63  fof(f245,plain,(
% 2.13/0.63    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_15)),
% 2.13/0.63    inference(subsumption_resolution,[],[f244,f95])).
% 2.13/0.63  fof(f244,plain,(
% 2.13/0.63    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_15)),
% 2.13/0.63    inference(subsumption_resolution,[],[f237,f90])).
% 2.13/0.63  fof(f237,plain,(
% 2.13/0.63    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_15),
% 2.13/0.63    inference(superposition,[],[f74,f231])).
% 2.13/0.63  fof(f74,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f38])).
% 2.13/0.63  fof(f272,plain,(
% 2.13/0.63    spl4_17 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_10),
% 2.13/0.63    inference(avatar_split_clause,[],[f227,f157,f135,f119,f93,f88,f83,f269])).
% 2.13/0.63  fof(f227,plain,(
% 2.13/0.63    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_10)),
% 2.13/0.63    inference(subsumption_resolution,[],[f226,f121])).
% 2.13/0.63  fof(f226,plain,(
% 2.13/0.63    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10)),
% 2.13/0.63    inference(resolution,[],[f225,f159])).
% 2.13/0.63  fof(f225,plain,(
% 2.13/0.63    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k6_tmap_1(sK0,X3) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X3,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f224,f137])).
% 2.13/0.63  fof(f224,plain,(
% 2.13/0.63    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3) | ~v3_pre_topc(X3,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f223,f137])).
% 2.13/0.63  fof(f223,plain,(
% 2.13/0.63    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3) | ~v3_pre_topc(X3,sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.13/0.63    inference(subsumption_resolution,[],[f222,f95])).
% 2.13/0.63  fof(f222,plain,(
% 2.13/0.63    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3) | ~v3_pre_topc(X3,sK0)) ) | (spl4_1 | ~spl4_2)),
% 2.13/0.63    inference(subsumption_resolution,[],[f100,f90])).
% 2.13/0.63  fof(f100,plain,(
% 2.13/0.63    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X3) | ~v3_pre_topc(X3,sK0)) ) | spl4_1),
% 2.13/0.63    inference(resolution,[],[f85,f65])).
% 2.13/0.63  fof(f65,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) )),
% 2.13/0.63    inference(cnf_transformation,[],[f29])).
% 2.13/0.63  fof(f29,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.63    inference(flattening,[],[f28])).
% 2.13/0.63  fof(f28,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.63    inference(ennf_transformation,[],[f13])).
% 2.13/0.63  fof(f13,axiom,(
% 2.13/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.13/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 2.13/0.63  fof(f232,plain,(
% 2.13/0.63    spl4_15 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10),
% 2.13/0.63    inference(avatar_split_clause,[],[f191,f157,f135,f93,f88,f83,f229])).
% 2.13/0.63  fof(f191,plain,(
% 2.13/0.63    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10)),
% 2.13/0.63    inference(resolution,[],[f185,f159])).
% 2.13/0.63  fof(f185,plain,(
% 2.13/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k6_tmap_1(sK0,X1)) = k2_struct_0(sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f184,f137])).
% 2.13/0.63  fof(f184,plain,(
% 2.13/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.63    inference(forward_demodulation,[],[f183,f137])).
% 2.13/0.63  fof(f183,plain,(
% 2.13/0.63    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.13/0.63    inference(subsumption_resolution,[],[f182,f95])).
% 2.13/0.63  fof(f182,plain,(
% 2.13/0.63    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | (spl4_1 | ~spl4_2)),
% 2.13/0.63    inference(subsumption_resolution,[],[f98,f90])).
% 2.13/0.63  fof(f98,plain,(
% 2.13/0.63    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) ) | spl4_1),
% 2.13/0.63    inference(resolution,[],[f85,f62])).
% 2.13/0.63  fof(f62,plain,(
% 2.13/0.63    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 2.13/0.63    inference(cnf_transformation,[],[f27])).
% 2.13/0.63  fof(f27,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.63    inference(flattening,[],[f26])).
% 2.13/0.63  fof(f26,plain,(
% 2.13/0.63    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.64    inference(ennf_transformation,[],[f11])).
% 2.13/0.64  fof(f11,axiom,(
% 2.13/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.13/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 2.13/0.64  fof(f221,plain,(
% 2.13/0.64    ~spl4_14 | spl4_9 | ~spl4_12),
% 2.13/0.64    inference(avatar_split_clause,[],[f192,f187,f140,f218])).
% 2.13/0.64  fof(f140,plain,(
% 2.13/0.64    spl4_9 <=> v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.13/0.64  fof(f192,plain,(
% 2.13/0.64    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | (spl4_9 | ~spl4_12)),
% 2.13/0.64    inference(superposition,[],[f141,f189])).
% 2.13/0.64  fof(f141,plain,(
% 2.13/0.64    ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | spl4_9),
% 2.13/0.64    inference(avatar_component_clause,[],[f140])).
% 2.13/0.64  fof(f190,plain,(
% 2.13/0.64    spl4_12 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10),
% 2.13/0.64    inference(avatar_split_clause,[],[f181,f157,f135,f93,f88,f83,f187])).
% 2.13/0.64  fof(f181,plain,(
% 2.13/0.64    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_10)),
% 2.13/0.64    inference(resolution,[],[f179,f159])).
% 2.13/0.64  fof(f179,plain,(
% 2.13/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.64    inference(forward_demodulation,[],[f178,f137])).
% 2.13/0.64  fof(f178,plain,(
% 2.13/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_8)),
% 2.13/0.64    inference(forward_demodulation,[],[f177,f137])).
% 2.13/0.64  fof(f177,plain,(
% 2.13/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 2.13/0.64    inference(subsumption_resolution,[],[f176,f95])).
% 2.13/0.64  fof(f176,plain,(
% 2.13/0.64    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_2)),
% 2.13/0.64    inference(subsumption_resolution,[],[f97,f90])).
% 2.13/0.64  fof(f97,plain,(
% 2.13/0.64    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) ) | spl4_1),
% 2.13/0.64    inference(resolution,[],[f85,f61])).
% 2.13/0.64  fof(f61,plain,(
% 2.13/0.64    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 2.13/0.64    inference(cnf_transformation,[],[f25])).
% 2.13/0.64  fof(f25,plain,(
% 2.13/0.64    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/0.64    inference(flattening,[],[f24])).
% 2.13/0.64  fof(f24,plain,(
% 2.13/0.64    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/0.64    inference(ennf_transformation,[],[f8])).
% 2.13/0.64  fof(f8,axiom,(
% 2.13/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.13/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 2.13/0.64  fof(f167,plain,(
% 2.13/0.64    spl4_11 | ~spl4_4 | ~spl4_8),
% 2.13/0.64    inference(avatar_split_clause,[],[f162,f135,f107,f164])).
% 2.13/0.64  fof(f162,plain,(
% 2.13/0.64    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) | (~spl4_4 | ~spl4_8)),
% 2.13/0.64    inference(forward_demodulation,[],[f117,f137])).
% 2.13/0.64  fof(f117,plain,(
% 2.13/0.64    sK1 = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),sK1) | ~spl4_4),
% 2.13/0.64    inference(resolution,[],[f109,f69])).
% 2.13/0.64  fof(f160,plain,(
% 2.13/0.64    spl4_10 | ~spl4_4 | ~spl4_8),
% 2.13/0.64    inference(avatar_split_clause,[],[f144,f135,f107,f157])).
% 2.13/0.64  fof(f144,plain,(
% 2.13/0.64    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_4 | ~spl4_8)),
% 2.13/0.64    inference(superposition,[],[f109,f137])).
% 2.13/0.64  fof(f138,plain,(
% 2.13/0.64    spl4_8 | ~spl4_5),
% 2.13/0.64    inference(avatar_split_clause,[],[f127,f112,f135])).
% 2.13/0.64  fof(f112,plain,(
% 2.13/0.64    spl4_5 <=> l1_struct_0(sK0)),
% 2.13/0.64    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.13/0.64  fof(f127,plain,(
% 2.13/0.64    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_5),
% 2.13/0.64    inference(resolution,[],[f114,f49])).
% 2.13/0.64  fof(f114,plain,(
% 2.13/0.64    l1_struct_0(sK0) | ~spl4_5),
% 2.13/0.64    inference(avatar_component_clause,[],[f112])).
% 2.13/0.64  fof(f115,plain,(
% 2.13/0.64    spl4_5 | ~spl4_3),
% 2.13/0.64    inference(avatar_split_clause,[],[f105,f93,f112])).
% 2.13/0.64  fof(f105,plain,(
% 2.13/0.64    l1_struct_0(sK0) | ~spl4_3),
% 2.13/0.64    inference(resolution,[],[f95,f52])).
% 2.13/0.64  fof(f110,plain,(
% 2.13/0.64    spl4_4),
% 2.13/0.64    inference(avatar_split_clause,[],[f45,f107])).
% 2.13/0.64  fof(f45,plain,(
% 2.13/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.13/0.64    inference(cnf_transformation,[],[f17])).
% 2.13/0.64  fof(f96,plain,(
% 2.13/0.64    spl4_3),
% 2.13/0.64    inference(avatar_split_clause,[],[f48,f93])).
% 2.13/0.64  fof(f48,plain,(
% 2.13/0.64    l1_pre_topc(sK0)),
% 2.13/0.64    inference(cnf_transformation,[],[f17])).
% 2.13/0.64  fof(f91,plain,(
% 2.13/0.64    spl4_2),
% 2.13/0.64    inference(avatar_split_clause,[],[f47,f88])).
% 2.13/0.64  fof(f47,plain,(
% 2.13/0.64    v2_pre_topc(sK0)),
% 2.13/0.64    inference(cnf_transformation,[],[f17])).
% 2.13/0.64  fof(f86,plain,(
% 2.13/0.64    ~spl4_1),
% 2.13/0.64    inference(avatar_split_clause,[],[f46,f83])).
% 2.13/0.64  fof(f46,plain,(
% 2.13/0.64    ~v2_struct_0(sK0)),
% 2.13/0.64    inference(cnf_transformation,[],[f17])).
% 2.13/0.64  % SZS output end Proof for theBenchmark
% 2.13/0.64  % (27080)------------------------------
% 2.13/0.64  % (27080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.64  % (27080)Termination reason: Refutation
% 2.13/0.64  
% 2.13/0.64  % (27080)Memory used [KB]: 12281
% 2.13/0.64  % (27080)Time elapsed: 0.210 s
% 2.13/0.64  % (27080)------------------------------
% 2.13/0.64  % (27080)------------------------------
% 2.13/0.64  % (27076)Success in time 0.276 s
%------------------------------------------------------------------------------
