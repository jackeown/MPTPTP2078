%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:27 EST 2020

% Result     : Theorem 41.89s
% Output     : Refutation 41.89s
% Verified   : 
% Statistics : Number of formulae       :  546 (1437 expanded)
%              Number of leaves         :  103 ( 551 expanded)
%              Depth                    :   28
%              Number of atoms          : 2579 (7519 expanded)
%              Number of equality atoms :  163 ( 891 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57969,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f450,f451,f456,f461,f471,f476,f477,f482,f487,f492,f497,f502,f512,f517,f527,f532,f597,f652,f657,f695,f752,f817,f925,f930,f992,f1704,f1811,f1813,f1830,f2162,f2258,f2342,f2395,f3496,f3652,f3654,f3675,f3721,f3733,f3739,f3760,f3775,f3780,f8815,f8913,f12222,f12417,f12566,f12568,f12680,f12707,f12710,f12770,f12795,f12797,f12915,f12927,f13075,f13078,f14308,f14339,f14426,f14545,f57834,f57842,f57926,f57958,f57968])).

fof(f57968,plain,
    ( ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_23
    | ~ spl29_82
    | ~ spl29_98
    | ~ spl29_379
    | spl29_527
    | ~ spl29_529 ),
    inference(avatar_contradiction_clause,[],[f57967])).

fof(f57967,plain,
    ( $false
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_23
    | ~ spl29_82
    | ~ spl29_98
    | ~ spl29_379
    | spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57966,f6186])).

fof(f6186,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl29_17
    | ~ spl29_23 ),
    inference(subsumption_resolution,[],[f6169,f526])).

fof(f526,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl29_17 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl29_17
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_17])])).

fof(f6169,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl29_23 ),
    inference(resolution,[],[f6166,f573])).

fof(f573,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f397,f395])).

fof(f395,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f236,f387])).

fof(f387,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f243,f235])).

fof(f235,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f243,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f236,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f397,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f240,f387])).

fof(f240,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f6166,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X3)
        | v1_funct_2(X3,k1_xboole_0,X2) )
    | ~ spl29_23 ),
    inference(subsumption_resolution,[],[f1595,f1298])).

fof(f1298,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | v1_partfun1(X3,k1_xboole_0) )
    | ~ spl29_23 ),
    inference(subsumption_resolution,[],[f1297,f614])).

fof(f614,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl29_23 ),
    inference(avatar_component_clause,[],[f612])).

fof(f612,plain,
    ( spl29_23
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_23])])).

fof(f1297,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_partfun1(X3,k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[],[f314,f429])).

fof(f429,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f346])).

fof(f346,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f210])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f314,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f1595,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_partfun1(X3,k1_xboole_0)
      | ~ v1_funct_1(X3)
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(superposition,[],[f358,f429])).

fof(f358,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f136])).

fof(f136,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f57966,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_82
    | ~ spl29_98
    | ~ spl29_379
    | spl29_527
    | ~ spl29_529 ),
    inference(forward_demodulation,[],[f57965,f8859])).

fof(f8859,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl29_379 ),
    inference(avatar_component_clause,[],[f8857])).

fof(f8857,plain,
    ( spl29_379
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_379])])).

fof(f57965,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_82
    | ~ spl29_98
    | spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57964,f496])).

fof(f496,plain,
    ( v2_pre_topc(sK0)
    | ~ spl29_11 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl29_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_11])])).

fof(f57964,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_17
    | ~ spl29_82
    | ~ spl29_98
    | spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57963,f491])).

fof(f491,plain,
    ( l1_pre_topc(sK0)
    | ~ spl29_10 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl29_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_10])])).

fof(f57963,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82
    | ~ spl29_98
    | spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57962,f14338])).

fof(f14338,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl29_529 ),
    inference(avatar_component_clause,[],[f14336])).

fof(f14336,plain,
    ( spl29_529
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_529])])).

fof(f57962,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82
    | ~ spl29_98
    | spl29_527 ),
    inference(subsumption_resolution,[],[f57960,f2306])).

fof(f2306,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl29_98 ),
    inference(avatar_component_clause,[],[f2304])).

fof(f2304,plain,
    ( spl29_98
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_98])])).

fof(f57960,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82
    | spl29_527 ),
    inference(resolution,[],[f14306,f13543])).

fof(f13543,plain,
    ( ! [X21] :
        ( v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(sK1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13542,f428])).

fof(f428,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f347])).

fof(f347,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f211])).

fof(f13542,plain,
    ( ! [X21] :
        ( ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13541,f237])).

fof(f237,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f13541,plain,
    ( ! [X21] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13540,f428])).

fof(f13540,plain,
    ( ! [X21] :
        ( ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13539,f526])).

fof(f13539,plain,
    ( ! [X21] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13538,f428])).

fof(f13538,plain,
    ( ! [X21] :
        ( ~ v5_pre_topc(k1_xboole_0,X21,sK1)
        | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13537,f428])).

fof(f13537,plain,
    ( ! [X21] :
        ( v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1)
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13536,f428])).

fof(f13536,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1)
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13535,f428])).

fof(f13535,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1)
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13534,f486])).

fof(f486,plain,
    ( v2_pre_topc(sK1)
    | ~ spl29_9 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl29_9
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_9])])).

fof(f13534,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1)
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_8
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13237,f481])).

fof(f481,plain,
    ( l1_pre_topc(sK1)
    | ~ spl29_8 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl29_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_8])])).

fof(f13237,plain,
    ( ! [X21] :
        ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1)
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X21)
        | ~ v2_pre_topc(X21) )
    | ~ spl29_82 ),
    inference(superposition,[],[f2090,f1931])).

fof(f1931,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_82 ),
    inference(avatar_component_clause,[],[f1929])).

fof(f1929,plain,
    ( spl29_82
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_82])])).

fof(f2090,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,X1)
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f440,f573])).

fof(f440,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f272])).

fof(f272,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f160,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,axiom,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f14306,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl29_527 ),
    inference(avatar_component_clause,[],[f14305])).

fof(f14305,plain,
    ( spl29_527
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_527])])).

fof(f57958,plain,
    ( spl29_98
    | ~ spl29_1
    | ~ spl29_97 ),
    inference(avatar_split_clause,[],[f57957,f2252,f443,f2304])).

fof(f443,plain,
    ( spl29_1
  <=> v5_pre_topc(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_1])])).

fof(f2252,plain,
    ( spl29_97
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_97])])).

fof(f57957,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl29_1
    | ~ spl29_97 ),
    inference(forward_demodulation,[],[f444,f2254])).

fof(f2254,plain,
    ( k1_xboole_0 = sK3
    | ~ spl29_97 ),
    inference(avatar_component_clause,[],[f2252])).

fof(f444,plain,
    ( v5_pre_topc(sK3,sK0,sK1)
    | ~ spl29_1 ),
    inference(avatar_component_clause,[],[f443])).

fof(f57926,plain,
    ( ~ spl29_527
    | ~ spl29_97
    | spl29_181 ),
    inference(avatar_split_clause,[],[f57925,f3693,f2252,f14305])).

fof(f3693,plain,
    ( spl29_181
  <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_181])])).

fof(f57925,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_97
    | spl29_181 ),
    inference(forward_demodulation,[],[f3694,f2254])).

fof(f3694,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl29_181 ),
    inference(avatar_component_clause,[],[f3693])).

fof(f57842,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != sK3
    | u1_struct_0(sK1) != k2_relat_1(sK3)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f57834,plain,
    ( ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_23
    | ~ spl29_82
    | spl29_98
    | ~ spl29_379
    | ~ spl29_527
    | ~ spl29_529 ),
    inference(avatar_contradiction_clause,[],[f57833])).

fof(f57833,plain,
    ( $false
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_23
    | ~ spl29_82
    | spl29_98
    | ~ spl29_379
    | ~ spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57832,f6186])).

fof(f57832,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_23
    | ~ spl29_82
    | spl29_98
    | ~ spl29_379
    | ~ spl29_527
    | ~ spl29_529 ),
    inference(forward_demodulation,[],[f57831,f8859])).

fof(f57831,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_23
    | ~ spl29_82
    | spl29_98
    | ~ spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57830,f614])).

fof(f57830,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_17
    | ~ spl29_82
    | spl29_98
    | ~ spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57829,f496])).

fof(f57829,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_17
    | ~ spl29_82
    | spl29_98
    | ~ spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57828,f491])).

fof(f57828,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82
    | spl29_98
    | ~ spl29_527
    | ~ spl29_529 ),
    inference(subsumption_resolution,[],[f57827,f14338])).

fof(f57827,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82
    | spl29_98
    | ~ spl29_527 ),
    inference(subsumption_resolution,[],[f57814,f2305])).

fof(f2305,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl29_98 ),
    inference(avatar_component_clause,[],[f2304])).

fof(f57814,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82
    | ~ spl29_527 ),
    inference(resolution,[],[f13586,f14317])).

fof(f14317,plain,
    ( ! [X0] :
        ( v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl29_527 ),
    inference(superposition,[],[f14307,f266])).

fof(f266,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f14307,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_527 ),
    inference(avatar_component_clause,[],[f14305])).

fof(f13586,plain,
    ( ! [X27] :
        ( ~ v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),u1_struct_0(sK1))
        | v5_pre_topc(k1_xboole_0,X27,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13585,f428])).

fof(f13585,plain,
    ( ! [X27] :
        ( ~ v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X27,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13584,f237])).

fof(f13584,plain,
    ( ! [X27] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X27,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13583,f428])).

fof(f13583,plain,
    ( ! [X27] :
        ( ~ v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X27,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_17
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13582,f526])).

fof(f13582,plain,
    ( ! [X27] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X27,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13581,f428])).

fof(f13581,plain,
    ( ! [X27] :
        ( ~ v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X27,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13580,f428])).

fof(f13580,plain,
    ( ! [X27] :
        ( v5_pre_topc(k1_xboole_0,X27,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13579,f428])).

fof(f13579,plain,
    ( ! [X27] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1)
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(forward_demodulation,[],[f13578,f428])).

fof(f13578,plain,
    ( ! [X27] :
        ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1)
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13577,f486])).

fof(f13577,plain,
    ( ! [X27] :
        ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1)
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_8
    | ~ spl29_82 ),
    inference(subsumption_resolution,[],[f13242,f481])).

fof(f13242,plain,
    ( ! [X27] :
        ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),k1_xboole_0)
        | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1)
        | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1))))
        | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X27)
        | ~ v2_pre_topc(X27) )
    | ~ spl29_82 ),
    inference(superposition,[],[f2124,f1931])).

fof(f2124,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,X1)
      | ~ v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
      | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f441,f573])).

fof(f441,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f273])).

fof(f273,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f160])).

fof(f14545,plain,
    ( spl29_50
    | spl29_23 ),
    inference(avatar_split_clause,[],[f14543,f612,f971])).

fof(f971,plain,
    ( spl29_50
  <=> ! [X5] : ~ v1_xboole_0(X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_50])])).

fof(f14543,plain,(
    ! [X1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X1) ) ),
    inference(superposition,[],[f290,f2550])).

fof(f2550,plain,(
    ! [X7] :
      ( k1_xboole_0 = sK12(X7)
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f962,f284])).

fof(f284,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f170])).

fof(f170,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f107,f169])).

fof(f169,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f962,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X17,sK12(X16))
      | ~ v1_xboole_0(X16) ) ),
    inference(resolution,[],[f373,f289])).

fof(f289,plain,(
    ! [X0] : m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( v1_xboole_0(sK12(X0))
      & m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f25,f175])).

fof(f175,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK12(X0))
        & m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f373,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f290,plain,(
    ! [X0] : v1_xboole_0(sK12(X0)) ),
    inference(cnf_transformation,[],[f176])).

fof(f14426,plain,
    ( spl29_379
    | ~ spl29_15
    | ~ spl29_18
    | ~ spl29_108 ),
    inference(avatar_split_clause,[],[f14422,f2354,f529,f514,f8857])).

fof(f514,plain,
    ( spl29_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_15])])).

fof(f529,plain,
    ( spl29_18
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_18])])).

fof(f2354,plain,
    ( spl29_108
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_108])])).

fof(f14422,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl29_15
    | ~ spl29_18
    | ~ spl29_108 ),
    inference(resolution,[],[f2356,f1437])).

fof(f1437,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl29_15
    | ~ spl29_18 ),
    inference(subsumption_resolution,[],[f1436,f531])).

fof(f531,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl29_18 ),
    inference(avatar_component_clause,[],[f529])).

fof(f1436,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_partfun1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl29_15 ),
    inference(subsumption_resolution,[],[f1420,f911])).

fof(f911,plain,(
    ! [X7] : v4_relat_1(k1_xboole_0,X7) ),
    inference(resolution,[],[f353,f237])).

fof(f353,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f133])).

fof(f133,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1420,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_partfun1(k1_xboole_0,X0)
        | ~ v4_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl29_15 ),
    inference(superposition,[],[f324,f516])).

fof(f516,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl29_15 ),
    inference(avatar_component_clause,[],[f514])).

fof(f324,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f2356,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl29_108 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f14339,plain,
    ( spl29_529
    | ~ spl29_82
    | ~ spl29_97
    | ~ spl29_179 ),
    inference(avatar_split_clause,[],[f14334,f3685,f2252,f1929,f14336])).

fof(f3685,plain,
    ( spl29_179
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_179])])).

fof(f14334,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl29_82
    | ~ spl29_97
    | ~ spl29_179 ),
    inference(forward_demodulation,[],[f14333,f2254])).

fof(f14333,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl29_82
    | ~ spl29_179 ),
    inference(forward_demodulation,[],[f3686,f1931])).

fof(f3686,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl29_179 ),
    inference(avatar_component_clause,[],[f3685])).

fof(f14308,plain,
    ( spl29_527
    | ~ spl29_97
    | ~ spl29_181 ),
    inference(avatar_split_clause,[],[f14303,f3693,f2252,f14305])).

fof(f14303,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_97
    | ~ spl29_181 ),
    inference(forward_demodulation,[],[f3695,f2254])).

fof(f3695,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_181 ),
    inference(avatar_component_clause,[],[f3693])).

fof(f13078,plain,
    ( spl29_101
    | ~ spl29_7
    | ~ spl29_97 ),
    inference(avatar_split_clause,[],[f13020,f2252,f473,f2319])).

fof(f2319,plain,
    ( spl29_101
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_101])])).

fof(f473,plain,
    ( spl29_7
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_7])])).

fof(f13020,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl29_7
    | ~ spl29_97 ),
    inference(superposition,[],[f475,f2254])).

fof(f475,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl29_7 ),
    inference(avatar_component_clause,[],[f473])).

fof(f13075,plain,
    ( ~ spl29_98
    | spl29_1
    | ~ spl29_97 ),
    inference(avatar_split_clause,[],[f13014,f2252,f443,f2304])).

fof(f13014,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl29_1
    | ~ spl29_97 ),
    inference(superposition,[],[f445,f2254])).

fof(f445,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | spl29_1 ),
    inference(avatar_component_clause,[],[f443])).

fof(f12927,plain,
    ( ~ spl29_25
    | ~ spl29_179
    | ~ spl29_181
    | spl29_2
    | ~ spl29_4
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(avatar_split_clause,[],[f12926,f3681,f2021,f494,f489,f458,f447,f3693,f3685,f621])).

fof(f621,plain,
    ( spl29_25
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_25])])).

fof(f447,plain,
    ( spl29_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_2])])).

fof(f458,plain,
    ( spl29_4
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).

fof(f2021,plain,
    ( spl29_86
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_86])])).

fof(f3681,plain,
    ( spl29_178
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_178])])).

fof(f12926,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_xboole_0(sK3)
    | ~ spl29_4
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(subsumption_resolution,[],[f12925,f496])).

fof(f12925,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK3)
    | ~ spl29_4
    | ~ spl29_10
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(subsumption_resolution,[],[f12924,f491])).

fof(f12924,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK3)
    | ~ spl29_4
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(subsumption_resolution,[],[f12923,f3682])).

fof(f3682,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_178 ),
    inference(avatar_component_clause,[],[f3681])).

fof(f12923,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK3)
    | ~ spl29_4
    | ~ spl29_86 ),
    inference(subsumption_resolution,[],[f10953,f2022])).

fof(f2022,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_86 ),
    inference(avatar_component_clause,[],[f2021])).

fof(f10953,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK3)
    | ~ spl29_4 ),
    inference(resolution,[],[f3006,f460])).

fof(f460,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl29_4 ),
    inference(avatar_component_clause,[],[f458])).

fof(f3006,plain,(
    ! [X17,X18,X16] :
      ( ~ v1_funct_2(X16,u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))),u1_struct_0(X18))
      | v5_pre_topc(X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)),X18)
      | ~ v5_pre_topc(X16,X17,X18)
      | ~ v1_funct_2(X16,u1_struct_0(X17),u1_struct_0(X18))
      | ~ l1_pre_topc(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | ~ v1_xboole_0(X16) ) ),
    inference(global_subsumption,[],[f2055])).

fof(f2055,plain,(
    ! [X6,X7,X5] :
      ( ~ v5_pre_topc(X5,X6,X7)
      | v5_pre_topc(X5,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),X7)
      | ~ v1_funct_2(X5,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))),u1_struct_0(X7))
      | ~ v1_funct_2(X5,u1_struct_0(X6),u1_struct_0(X7))
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | ~ v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f2054,f550])).

fof(f550,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f237,f266])).

fof(f2054,plain,(
    ! [X6,X7,X5] :
      ( ~ v5_pre_topc(X5,X6,X7)
      | v5_pre_topc(X5,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),X7)
      | ~ v1_funct_2(X5,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))),u1_struct_0(X7))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X5,u1_struct_0(X6),u1_struct_0(X7))
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | ~ v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f2046,f265])).

fof(f265,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f2046,plain,(
    ! [X6,X7,X5] :
      ( ~ v5_pre_topc(X5,X6,X7)
      | v5_pre_topc(X5,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),X7)
      | ~ v1_funct_2(X5,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))),u1_struct_0(X7))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
      | ~ v1_funct_2(X5,u1_struct_0(X6),u1_struct_0(X7))
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f438,f550])).

fof(f438,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f274])).

fof(f274,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f161,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
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
    inference(nnf_transformation,[],[f101])).

fof(f101,plain,(
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
    inference(flattening,[],[f100])).

fof(f100,plain,(
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
    inference(ennf_transformation,[],[f78])).

fof(f78,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f12915,plain,
    ( ~ spl29_2
    | ~ spl29_179
    | ~ spl29_180
    | spl29_181
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_30
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(avatar_split_clause,[],[f12914,f3681,f2021,f692,f494,f489,f463,f458,f3693,f3689,f3685,f447])).

fof(f3689,plain,
    ( spl29_180
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_180])])).

fof(f463,plain,
    ( spl29_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_5])])).

fof(f692,plain,
    ( spl29_30
  <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_30])])).

fof(f12914,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_30
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(subsumption_resolution,[],[f12913,f496])).

fof(f12913,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_10
    | ~ spl29_30
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(subsumption_resolution,[],[f12912,f491])).

fof(f12912,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_30
    | ~ spl29_86
    | ~ spl29_178 ),
    inference(subsumption_resolution,[],[f12911,f3682])).

fof(f12911,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_30
    | ~ spl29_86 ),
    inference(subsumption_resolution,[],[f12910,f2022])).

fof(f12910,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_30 ),
    inference(subsumption_resolution,[],[f12909,f465])).

fof(f465,plain,
    ( v1_funct_1(sK3)
    | ~ spl29_5 ),
    inference(avatar_component_clause,[],[f463])).

fof(f12909,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_30 ),
    inference(subsumption_resolution,[],[f11227,f460])).

fof(f11227,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_30 ),
    inference(resolution,[],[f2068,f694])).

fof(f694,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl29_30 ),
    inference(avatar_component_clause,[],[f692])).

fof(f2068,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),u1_struct_0(X4)))
      | v5_pre_topc(X2,X3,X4)
      | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),u1_struct_0(X4))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
      | ~ v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4) ) ),
    inference(resolution,[],[f439,f344])).

fof(f344,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f439,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f414])).

fof(f414,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f275])).

fof(f275,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f12797,plain,
    ( spl29_175
    | ~ spl29_79
    | ~ spl29_5
    | ~ spl29_176 ),
    inference(avatar_split_clause,[],[f12796,f3668,f463,f1787,f3664])).

fof(f3664,plain,
    ( spl29_175
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_175])])).

fof(f1787,plain,
    ( spl29_79
  <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_79])])).

fof(f3668,plain,
    ( spl29_176
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_176])])).

fof(f12796,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl29_5
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12248,f465])).

fof(f12248,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(sK3)
    | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl29_176 ),
    inference(resolution,[],[f3669,f358])).

fof(f3669,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl29_176 ),
    inference(avatar_component_clause,[],[f3668])).

fof(f12795,plain,
    ( ~ spl29_175
    | spl29_177
    | ~ spl29_1
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_176 ),
    inference(avatar_split_clause,[],[f12794,f3668,f494,f489,f484,f479,f473,f468,f463,f443,f3672,f3664])).

fof(f3672,plain,
    ( spl29_177
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_177])])).

fof(f468,plain,
    ( spl29_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_6])])).

fof(f12794,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12793,f496])).

fof(f12793,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12792,f491])).

fof(f12792,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12791,f486])).

fof(f12791,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12790,f481])).

fof(f12790,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12789,f475])).

fof(f12789,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12788,f470])).

fof(f470,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl29_6 ),
    inference(avatar_component_clause,[],[f468])).

fof(f12788,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12237,f465])).

fof(f12237,plain,
    ( ~ v5_pre_topc(sK3,sK0,sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_176 ),
    inference(resolution,[],[f3669,f438])).

fof(f12770,plain,
    ( ~ spl29_175
    | spl29_1
    | ~ spl29_177
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_176 ),
    inference(avatar_split_clause,[],[f12769,f3668,f494,f489,f484,f479,f473,f468,f463,f3672,f443,f3664])).

fof(f12769,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_11
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12768,f496])).

fof(f12768,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_10
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12767,f491])).

fof(f12767,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_9
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12766,f486])).

fof(f12766,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_8
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12765,f481])).

fof(f12765,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12764,f475])).

fof(f12764,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12763,f470])).

fof(f12763,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_5
    | ~ spl29_176 ),
    inference(subsumption_resolution,[],[f12236,f465])).

fof(f12236,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,sK0,sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl29_176 ),
    inference(resolution,[],[f3669,f439])).

fof(f12710,plain,
    ( spl29_61
    | spl29_79
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_30 ),
    inference(avatar_split_clause,[],[f12709,f692,f463,f458,f1787,f1226])).

fof(f1226,plain,
    ( spl29_61
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_61])])).

fof(f12709,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_30 ),
    inference(subsumption_resolution,[],[f12708,f460])).

fof(f12708,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl29_5
    | ~ spl29_30 ),
    inference(subsumption_resolution,[],[f7518,f465])).

fof(f7518,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl29_30 ),
    inference(resolution,[],[f1759,f694])).

fof(f1759,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X4,X5))
      | ~ v1_funct_1(X3)
      | v1_partfun1(X3,X4)
      | v1_xboole_0(X5)
      | ~ v1_funct_2(X3,X4,X5) ) ),
    inference(resolution,[],[f310,f344])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f12707,plain,
    ( spl29_82
    | spl29_79
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_30 ),
    inference(avatar_split_clause,[],[f12706,f692,f463,f458,f1787,f1929])).

fof(f12706,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_30 ),
    inference(subsumption_resolution,[],[f12705,f465])).

fof(f12705,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_4
    | ~ spl29_30 ),
    inference(subsumption_resolution,[],[f8019,f460])).

fof(f8019,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl29_30 ),
    inference(resolution,[],[f1909,f694])).

fof(f1909,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X5,X3))
      | v1_partfun1(X4,X5)
      | ~ v1_funct_2(X4,X5,X3)
      | ~ v1_funct_1(X4)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f436,f344])).

fof(f436,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f141])).

fof(f141,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f140])).

fof(f140,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f70,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f12680,plain,
    ( spl29_25
    | ~ spl29_61
    | ~ spl29_30 ),
    inference(avatar_split_clause,[],[f4171,f692,f1226,f621])).

fof(f4171,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(sK3)
    | ~ spl29_30 ),
    inference(resolution,[],[f1206,f694])).

fof(f1206,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X4,X3))
      | ~ v1_xboole_0(X3)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f313,f344])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f12568,plain,
    ( ~ spl29_25
    | ~ spl29_14
    | spl29_187 ),
    inference(avatar_split_clause,[],[f12567,f3772,f509,f621])).

fof(f509,plain,
    ( spl29_14
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_14])])).

fof(f3772,plain,
    ( spl29_187
  <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_187])])).

fof(f12567,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl29_14
    | spl29_187 ),
    inference(subsumption_resolution,[],[f3783,f568])).

fof(f568,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f567,f266])).

fof(f567,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f533,f395])).

fof(f533,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(global_subsumption,[],[f237,f417])).

fof(f417,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f406])).

fof(f406,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f316,f235])).

fof(f316,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f3783,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK1))
    | ~ v1_xboole_0(sK3)
    | ~ spl29_14
    | spl29_187 ),
    inference(superposition,[],[f3774,f553])).

fof(f553,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl29_14 ),
    inference(superposition,[],[f511,f266])).

fof(f511,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl29_14 ),
    inference(avatar_component_clause,[],[f509])).

fof(f3774,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | spl29_187 ),
    inference(avatar_component_clause,[],[f3772])).

fof(f12566,plain,
    ( ~ spl29_25
    | spl29_180 ),
    inference(avatar_split_clause,[],[f3787,f3689,f621])).

fof(f3787,plain,
    ( ~ v1_xboole_0(sK3)
    | spl29_180 ),
    inference(resolution,[],[f3691,f550])).

fof(f3691,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl29_180 ),
    inference(avatar_component_clause,[],[f3689])).

fof(f12417,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f12222,plain,
    ( ~ spl29_28
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_46
    | ~ spl29_78
    | ~ spl29_79
    | spl29_188 ),
    inference(avatar_contradiction_clause,[],[f12221])).

fof(f12221,plain,
    ( $false
    | ~ spl29_28
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_46
    | ~ spl29_78
    | ~ spl29_79
    | spl29_188 ),
    inference(subsumption_resolution,[],[f12220,f929])).

fof(f929,plain,
    ( v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl29_46 ),
    inference(avatar_component_clause,[],[f927])).

fof(f927,plain,
    ( spl29_46
  <=> v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_46])])).

fof(f12220,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl29_28
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_78
    | ~ spl29_79
    | spl29_188 ),
    inference(subsumption_resolution,[],[f12194,f1789])).

fof(f1789,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl29_79 ),
    inference(avatar_component_clause,[],[f1787])).

fof(f12194,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl29_28
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_78
    | spl29_188 ),
    inference(resolution,[],[f7790,f3779])).

fof(f3779,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | spl29_188 ),
    inference(avatar_component_clause,[],[f3777])).

fof(f3777,plain,
    ( spl29_188
  <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_188])])).

fof(f7790,plain,
    ( ! [X5] :
        ( r1_tarski(sK3,k2_zfmisc_1(X5,u1_struct_0(sK1)))
        | ~ v1_partfun1(sK3,X5)
        | ~ v4_relat_1(sK3,X5) )
    | ~ spl29_28
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_78 ),
    inference(superposition,[],[f651,f7767])).

fof(f7767,plain,
    ( ! [X17] :
        ( u1_struct_0(sK0) = X17
        | ~ v1_partfun1(sK3,X17)
        | ~ v4_relat_1(sK3,X17) )
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_78 ),
    inference(subsumption_resolution,[],[f7766,f816])).

fof(f816,plain,
    ( v1_relat_1(sK3)
    | ~ spl29_39 ),
    inference(avatar_component_clause,[],[f814])).

fof(f814,plain,
    ( spl29_39
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_39])])).

fof(f7766,plain,
    ( ! [X17] :
        ( u1_struct_0(sK0) = X17
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X17)
        | ~ v4_relat_1(sK3,X17) )
    | ~ spl29_45
    | ~ spl29_78 ),
    inference(subsumption_resolution,[],[f7744,f924])).

fof(f924,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl29_45 ),
    inference(avatar_component_clause,[],[f922])).

fof(f922,plain,
    ( spl29_45
  <=> v4_relat_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_45])])).

fof(f7744,plain,
    ( ! [X17] :
        ( u1_struct_0(sK0) = X17
        | ~ v4_relat_1(sK3,u1_struct_0(sK0))
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X17)
        | ~ v4_relat_1(sK3,X17) )
    | ~ spl29_78 ),
    inference(resolution,[],[f1435,f1781])).

fof(f1781,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK0))
    | ~ spl29_78 ),
    inference(avatar_component_clause,[],[f1779])).

fof(f1779,plain,
    ( spl29_78
  <=> v1_partfun1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_78])])).

fof(f1435,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_partfun1(X3,X5)
      | X4 = X5
      | ~ v4_relat_1(X3,X5)
      | ~ v1_relat_1(X3)
      | ~ v1_partfun1(X3,X4)
      | ~ v4_relat_1(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f1422])).

fof(f1422,plain,(
    ! [X4,X5,X3] :
      ( X4 = X5
      | ~ v1_partfun1(X3,X5)
      | ~ v4_relat_1(X3,X5)
      | ~ v1_relat_1(X3)
      | ~ v1_partfun1(X3,X4)
      | ~ v4_relat_1(X3,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f324,f324])).

fof(f651,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl29_28 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl29_28
  <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_28])])).

fof(f8913,plain,
    ( ~ spl29_23
    | ~ spl29_101
    | spl29_108
    | spl29_169 ),
    inference(avatar_contradiction_clause,[],[f8912])).

fof(f8912,plain,
    ( $false
    | ~ spl29_23
    | ~ spl29_101
    | spl29_108
    | spl29_169 ),
    inference(subsumption_resolution,[],[f8911,f614])).

fof(f8911,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_101
    | spl29_108
    | spl29_169 ),
    inference(subsumption_resolution,[],[f8910,f3495])).

fof(f3495,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl29_169 ),
    inference(avatar_component_clause,[],[f3493])).

fof(f3493,plain,
    ( spl29_169
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_169])])).

fof(f8910,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_101
    | spl29_108 ),
    inference(subsumption_resolution,[],[f8892,f2355])).

fof(f2355,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | spl29_108 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f8892,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl29_101 ),
    inference(resolution,[],[f2321,f3012])).

fof(f3012,plain,(
    ! [X19,X17,X18] :
      ( ~ v1_funct_2(X18,X19,X17)
      | v1_partfun1(X18,X19)
      | k1_xboole_0 = X17
      | ~ v1_xboole_0(X18) ) ),
    inference(global_subsumption,[],[f1924])).

fof(f1924,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 = X6
      | v1_partfun1(X7,X8)
      | ~ v1_funct_2(X7,X8,X6)
      | ~ v1_xboole_0(X7) ) ),
    inference(subsumption_resolution,[],[f1910,f265])).

fof(f1910,plain,(
    ! [X6,X8,X7] :
      ( k1_xboole_0 = X6
      | v1_partfun1(X7,X8)
      | ~ v1_funct_2(X7,X8,X6)
      | ~ v1_funct_1(X7)
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f436,f550])).

fof(f2321,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl29_101 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f8815,plain,
    ( ~ spl29_7
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_46
    | ~ spl29_78
    | ~ spl29_79
    | spl29_175 ),
    inference(avatar_contradiction_clause,[],[f8814])).

fof(f8814,plain,
    ( $false
    | ~ spl29_7
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_46
    | ~ spl29_78
    | ~ spl29_79
    | spl29_175 ),
    inference(subsumption_resolution,[],[f8813,f929])).

fof(f8813,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl29_7
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_78
    | ~ spl29_79
    | spl29_175 ),
    inference(subsumption_resolution,[],[f8807,f1789])).

fof(f8807,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl29_7
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_78
    | spl29_175 ),
    inference(resolution,[],[f7789,f3666])).

fof(f3666,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl29_175 ),
    inference(avatar_component_clause,[],[f3664])).

fof(f7789,plain,
    ( ! [X4] :
        ( v1_funct_2(sK3,X4,u1_struct_0(sK1))
        | ~ v1_partfun1(sK3,X4)
        | ~ v4_relat_1(sK3,X4) )
    | ~ spl29_7
    | ~ spl29_39
    | ~ spl29_45
    | ~ spl29_78 ),
    inference(superposition,[],[f475,f7767])).

fof(f3780,plain,
    ( ~ spl29_188
    | spl29_176 ),
    inference(avatar_split_clause,[],[f3766,f3668,f3777])).

fof(f3766,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))
    | spl29_176 ),
    inference(resolution,[],[f3670,f344])).

fof(f3670,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl29_176 ),
    inference(avatar_component_clause,[],[f3668])).

fof(f3775,plain,
    ( ~ spl29_187
    | ~ spl29_3
    | spl29_176 ),
    inference(avatar_split_clause,[],[f3765,f3668,f453,f3772])).

fof(f453,plain,
    ( spl29_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).

fof(f3765,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ spl29_3
    | spl29_176 ),
    inference(resolution,[],[f3670,f1672])).

fof(f1672,plain,
    ( ! [X17] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X17)))
        | ~ r1_tarski(k2_relat_1(sK3),X17) )
    | ~ spl29_3 ),
    inference(resolution,[],[f376,f455])).

fof(f455,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl29_3 ),
    inference(avatar_component_clause,[],[f453])).

fof(f376,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f146])).

fof(f146,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f3760,plain,
    ( ~ spl29_186
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_78
    | spl29_179 ),
    inference(avatar_split_clause,[],[f3755,f3685,f1779,f468,f463,f3757])).

fof(f3757,plain,
    ( spl29_186
  <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_186])])).

fof(f3755,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_78
    | spl29_179 ),
    inference(resolution,[],[f3687,f2214])).

fof(f2214,plain,
    ( ! [X11] :
        ( v1_funct_2(sK3,u1_struct_0(sK0),X11)
        | ~ r1_tarski(k2_relat_1(sK3),X11) )
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_78 ),
    inference(subsumption_resolution,[],[f2213,f465])).

fof(f2213,plain,
    ( ! [X11] :
        ( ~ r1_tarski(k2_relat_1(sK3),X11)
        | ~ v1_funct_1(sK3)
        | v1_funct_2(sK3,u1_struct_0(sK0),X11) )
    | ~ spl29_6
    | ~ spl29_78 ),
    inference(subsumption_resolution,[],[f2188,f1781])).

fof(f2188,plain,
    ( ! [X11] :
        ( ~ r1_tarski(k2_relat_1(sK3),X11)
        | ~ v1_partfun1(sK3,u1_struct_0(sK0))
        | ~ v1_funct_1(sK3)
        | v1_funct_2(sK3,u1_struct_0(sK0),X11) )
    | ~ spl29_6 ),
    inference(resolution,[],[f1671,f358])).

fof(f1671,plain,
    ( ! [X16] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X16)))
        | ~ r1_tarski(k2_relat_1(sK3),X16) )
    | ~ spl29_6 ),
    inference(resolution,[],[f376,f470])).

fof(f3687,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl29_179 ),
    inference(avatar_component_clause,[],[f3685])).

fof(f3739,plain,
    ( ~ spl29_8
    | ~ spl29_9
    | spl29_178 ),
    inference(avatar_contradiction_clause,[],[f3738])).

fof(f3738,plain,
    ( $false
    | ~ spl29_8
    | ~ spl29_9
    | spl29_178 ),
    inference(subsumption_resolution,[],[f3737,f486])).

fof(f3737,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl29_8
    | spl29_178 ),
    inference(subsumption_resolution,[],[f3735,f481])).

fof(f3735,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl29_178 ),
    inference(resolution,[],[f3683,f270])).

fof(f270,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f3683,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl29_178 ),
    inference(avatar_component_clause,[],[f3681])).

fof(f3733,plain,
    ( ~ spl29_10
    | ~ spl29_11
    | spl29_174 ),
    inference(avatar_contradiction_clause,[],[f3732])).

fof(f3732,plain,
    ( $false
    | ~ spl29_10
    | ~ spl29_11
    | spl29_174 ),
    inference(subsumption_resolution,[],[f3731,f496])).

fof(f3731,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl29_10
    | spl29_174 ),
    inference(subsumption_resolution,[],[f3729,f491])).

fof(f3729,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl29_174 ),
    inference(resolution,[],[f3662,f270])).

fof(f3662,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl29_174 ),
    inference(avatar_component_clause,[],[f3660])).

fof(f3660,plain,
    ( spl29_174
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_174])])).

fof(f3721,plain,
    ( ~ spl29_174
    | ~ spl29_85
    | ~ spl29_175
    | ~ spl29_176
    | spl29_2
    | ~ spl29_177
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_8
    | ~ spl29_9 ),
    inference(avatar_split_clause,[],[f3720,f484,f479,f463,f458,f453,f3672,f447,f3668,f3664,f2017,f3660])).

fof(f2017,plain,
    ( spl29_85
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_85])])).

fof(f3720,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_8
    | ~ spl29_9 ),
    inference(subsumption_resolution,[],[f3719,f486])).

fof(f3719,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_8 ),
    inference(subsumption_resolution,[],[f3718,f481])).

fof(f3718,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5 ),
    inference(subsumption_resolution,[],[f3717,f465])).

fof(f3717,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4 ),
    inference(subsumption_resolution,[],[f2095,f460])).

fof(f2095,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3 ),
    inference(resolution,[],[f440,f455])).

fof(f3675,plain,
    ( ~ spl29_174
    | ~ spl29_85
    | ~ spl29_175
    | ~ spl29_176
    | spl29_177
    | ~ spl29_2
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_8
    | ~ spl29_9 ),
    inference(avatar_split_clause,[],[f3658,f484,f479,f463,f458,f453,f447,f3672,f3668,f3664,f2017,f3660])).

fof(f3658,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_8
    | ~ spl29_9 ),
    inference(subsumption_resolution,[],[f3657,f486])).

fof(f3657,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5
    | ~ spl29_8 ),
    inference(subsumption_resolution,[],[f3656,f481])).

fof(f3656,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4
    | ~ spl29_5 ),
    inference(subsumption_resolution,[],[f3655,f465])).

fof(f3655,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3
    | ~ spl29_4 ),
    inference(subsumption_resolution,[],[f2129,f460])).

fof(f2129,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl29_3 ),
    inference(resolution,[],[f441,f455])).

fof(f3654,plain,
    ( ~ spl29_8
    | spl29_86 ),
    inference(avatar_contradiction_clause,[],[f3653])).

fof(f3653,plain,
    ( $false
    | ~ spl29_8
    | spl29_86 ),
    inference(subsumption_resolution,[],[f3648,f481])).

fof(f3648,plain,
    ( ~ l1_pre_topc(sK1)
    | spl29_86 ),
    inference(resolution,[],[f887,f2023])).

fof(f2023,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl29_86 ),
    inference(avatar_component_clause,[],[f2021])).

fof(f887,plain,(
    ! [X6] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f318,f256])).

fof(f256,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f74])).

fof(f74,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f3652,plain,
    ( ~ spl29_10
    | spl29_85 ),
    inference(avatar_contradiction_clause,[],[f3651])).

fof(f3651,plain,
    ( $false
    | ~ spl29_10
    | spl29_85 ),
    inference(subsumption_resolution,[],[f3647,f491])).

fof(f3647,plain,
    ( ~ l1_pre_topc(sK0)
    | spl29_85 ),
    inference(resolution,[],[f887,f2019])).

fof(f2019,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl29_85 ),
    inference(avatar_component_clause,[],[f2017])).

fof(f3496,plain,
    ( ~ spl29_169
    | ~ spl29_14
    | spl29_105 ),
    inference(avatar_split_clause,[],[f3491,f2339,f509,f3493])).

fof(f2339,plain,
    ( spl29_105
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_105])])).

fof(f3491,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | ~ spl29_14
    | spl29_105 ),
    inference(forward_demodulation,[],[f3490,f511])).

fof(f3490,plain,
    ( k2_relat_1(k1_xboole_0) != u1_struct_0(sK1)
    | spl29_105 ),
    inference(subsumption_resolution,[],[f3489,f237])).

fof(f3489,plain,
    ( k2_relat_1(k1_xboole_0) != u1_struct_0(sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl29_105 ),
    inference(superposition,[],[f2341,f352])).

fof(f352,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f132])).

fof(f132,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2341,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0)
    | spl29_105 ),
    inference(avatar_component_clause,[],[f2339])).

fof(f2395,plain,
    ( ~ spl29_25
    | spl29_97 ),
    inference(avatar_contradiction_clause,[],[f2392])).

fof(f2392,plain,
    ( $false
    | ~ spl29_25
    | spl29_97 ),
    inference(unit_resulting_resolution,[],[f623,f2253,f266])).

fof(f2253,plain,
    ( k1_xboole_0 != sK3
    | spl29_97 ),
    inference(avatar_component_clause,[],[f2252])).

fof(f623,plain,
    ( v1_xboole_0(sK3)
    | ~ spl29_25 ),
    inference(avatar_component_clause,[],[f621])).

fof(f2342,plain,
    ( ~ spl29_105
    | spl29_71
    | ~ spl29_97 ),
    inference(avatar_split_clause,[],[f2292,f2252,f1697,f2339])).

fof(f1697,plain,
    ( spl29_71
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_71])])).

fof(f2292,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0)
    | spl29_71
    | ~ spl29_97 ),
    inference(superposition,[],[f1698,f2254])).

fof(f1698,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3)
    | spl29_71 ),
    inference(avatar_component_clause,[],[f1697])).

fof(f2258,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK13(k1_xboole_0)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(sK13(k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2162,plain,
    ( spl29_77
    | ~ spl29_6
    | ~ spl29_71 ),
    inference(avatar_split_clause,[],[f2161,f1697,f468,f1753])).

fof(f1753,plain,
    ( spl29_77
  <=> u1_struct_0(sK1) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_77])])).

fof(f2161,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK3)
    | ~ spl29_6
    | ~ spl29_71 ),
    inference(subsumption_resolution,[],[f2147,f470])).

fof(f2147,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl29_71 ),
    inference(superposition,[],[f1699,f352])).

fof(f1699,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3)
    | ~ spl29_71 ),
    inference(avatar_component_clause,[],[f1697])).

fof(f1830,plain,
    ( ~ spl29_60
    | ~ spl29_6
    | spl29_25 ),
    inference(avatar_split_clause,[],[f1218,f621,f468,f1220])).

fof(f1220,plain,
    ( spl29_60
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_60])])).

fof(f1218,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl29_6
    | spl29_25 ),
    inference(subsumption_resolution,[],[f1210,f622])).

fof(f622,plain,
    ( ~ v1_xboole_0(sK3)
    | spl29_25 ),
    inference(avatar_component_clause,[],[f621])).

fof(f1210,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl29_6 ),
    inference(resolution,[],[f313,f470])).

fof(f1813,plain,
    ( spl29_78
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | spl29_60 ),
    inference(avatar_split_clause,[],[f1777,f1220,f473,f468,f463,f1779])).

fof(f1777,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK0))
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7
    | spl29_60 ),
    inference(subsumption_resolution,[],[f1776,f1222])).

fof(f1222,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl29_60 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f1776,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl29_5
    | ~ spl29_6
    | ~ spl29_7 ),
    inference(subsumption_resolution,[],[f1775,f465])).

fof(f1775,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl29_6
    | ~ spl29_7 ),
    inference(subsumption_resolution,[],[f1763,f475])).

fof(f1763,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl29_6 ),
    inference(resolution,[],[f310,f470])).

fof(f1811,plain,
    ( ~ spl29_60
    | ~ spl29_12
    | spl29_72 ),
    inference(avatar_split_clause,[],[f1801,f1701,f499,f1220])).

fof(f499,plain,
    ( spl29_12
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_12])])).

fof(f1701,plain,
    ( spl29_72
  <=> r1_tarski(k6_partfun1(u1_struct_0(sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_72])])).

fof(f1801,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl29_12
    | spl29_72 ),
    inference(subsumption_resolution,[],[f1717,f568])).

fof(f1717,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK3)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl29_12
    | spl29_72 ),
    inference(superposition,[],[f1703,f552])).

fof(f552,plain,
    ( ! [X0] :
        ( k6_partfun1(X0) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl29_12 ),
    inference(superposition,[],[f501,f266])).

fof(f501,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl29_12 ),
    inference(avatar_component_clause,[],[f499])).

fof(f1703,plain,
    ( ~ r1_tarski(k6_partfun1(u1_struct_0(sK1)),sK3)
    | spl29_72 ),
    inference(avatar_component_clause,[],[f1701])).

fof(f1704,plain,
    ( spl29_71
    | ~ spl29_72
    | ~ spl29_6 ),
    inference(avatar_split_clause,[],[f1687,f468,f1701,f1697])).

fof(f1687,plain,
    ( ~ r1_tarski(k6_partfun1(u1_struct_0(sK1)),sK3)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3)
    | ~ spl29_6 ),
    inference(resolution,[],[f410,f470])).

fof(f410,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k6_partfun1(X1),X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(definition_unfolding,[],[f356,f239])).

fof(f239,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
        & r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f134])).

fof(f134,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
        & r1_tarski(X1,k1_relset_1(X0,X1,X2)) )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( k2_relset_1(X0,X1,X2) = X1
          & r1_tarski(X1,k1_relset_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

fof(f992,plain,(
    ~ spl29_50 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | ~ spl29_50 ),
    inference(subsumption_resolution,[],[f290,f972])).

fof(f972,plain,
    ( ! [X5] : ~ v1_xboole_0(X5)
    | ~ spl29_50 ),
    inference(avatar_component_clause,[],[f971])).

fof(f930,plain,
    ( spl29_46
    | ~ spl29_3 ),
    inference(avatar_split_clause,[],[f914,f453,f927])).

fof(f914,plain,
    ( v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl29_3 ),
    inference(resolution,[],[f353,f455])).

fof(f925,plain,
    ( spl29_45
    | ~ spl29_6 ),
    inference(avatar_split_clause,[],[f913,f468,f922])).

fof(f913,plain,
    ( v4_relat_1(sK3,u1_struct_0(sK0))
    | ~ spl29_6 ),
    inference(resolution,[],[f353,f470])).

fof(f817,plain,
    ( spl29_39
    | ~ spl29_6 ),
    inference(avatar_split_clause,[],[f805,f468,f814])).

fof(f805,plain,
    ( v1_relat_1(sK3)
    | ~ spl29_6 ),
    inference(resolution,[],[f351,f470])).

fof(f351,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f752,plain,
    ( spl29_35
    | ~ spl29_29 ),
    inference(avatar_split_clause,[],[f746,f654,f749])).

fof(f749,plain,
    ( spl29_35
  <=> k1_xboole_0 = sK13(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_35])])).

fof(f654,plain,
    ( spl29_29
  <=> r1_tarski(sK13(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_29])])).

fof(f746,plain,
    ( k1_xboole_0 = sK13(k1_xboole_0)
    | ~ spl29_29 ),
    inference(resolution,[],[f656,f268])).

fof(f268,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f656,plain,
    ( r1_tarski(sK13(k1_xboole_0),k1_xboole_0)
    | ~ spl29_29 ),
    inference(avatar_component_clause,[],[f654])).

fof(f695,plain,
    ( spl29_30
    | ~ spl29_3 ),
    inference(avatar_split_clause,[],[f689,f453,f692])).

fof(f689,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl29_3 ),
    inference(resolution,[],[f455,f343])).

fof(f343,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f209])).

fof(f657,plain,
    ( spl29_29
    | ~ spl29_21 ),
    inference(avatar_split_clause,[],[f645,f593,f654])).

fof(f593,plain,
    ( spl29_21
  <=> m1_subset_1(sK13(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_21])])).

fof(f645,plain,
    ( r1_tarski(sK13(k1_xboole_0),k1_xboole_0)
    | ~ spl29_21 ),
    inference(resolution,[],[f343,f595])).

fof(f595,plain,
    ( m1_subset_1(sK13(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl29_21 ),
    inference(avatar_component_clause,[],[f593])).

fof(f652,plain,
    ( spl29_28
    | ~ spl29_6 ),
    inference(avatar_split_clause,[],[f642,f468,f649])).

fof(f642,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl29_6 ),
    inference(resolution,[],[f343,f470])).

fof(f597,plain,(
    spl29_21 ),
    inference(avatar_split_clause,[],[f591,f593])).

fof(f591,plain,(
    m1_subset_1(sK13(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f291,f429])).

fof(f291,plain,(
    ! [X0] : m1_subset_1(sK13(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( v3_funct_2(sK13(X0),X0,X0)
      & v1_funct_2(sK13(X0),X0,X0)
      & v1_funct_1(sK13(X0))
      & v5_relat_1(sK13(X0),X0)
      & v4_relat_1(sK13(X0),X0)
      & v1_relat_1(sK13(X0))
      & m1_subset_1(sK13(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f68,f177])).

fof(f177,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1)
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
     => ( v3_funct_2(sK13(X0),X0,X0)
        & v1_funct_2(sK13(X0),X0,X0)
        & v1_funct_1(sK13(X0))
        & v5_relat_1(sK13(X0),X0)
        & v4_relat_1(sK13(X0),X0)
        & v1_relat_1(sK13(X0))
        & m1_subset_1(sK13(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,axiom,(
    ! [X0] :
    ? [X1] :
      ( v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v4_relat_1(X1,X0)
      & v1_relat_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_2)).

fof(f532,plain,(
    spl29_18 ),
    inference(avatar_split_clause,[],[f244,f529])).

fof(f244,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f527,plain,(
    spl29_17 ),
    inference(avatar_split_clause,[],[f246,f524])).

fof(f246,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

fof(f517,plain,(
    spl29_15 ),
    inference(avatar_split_clause,[],[f233,f514])).

fof(f233,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f512,plain,(
    spl29_14 ),
    inference(avatar_split_clause,[],[f234,f509])).

fof(f234,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

fof(f502,plain,(
    spl29_12 ),
    inference(avatar_split_clause,[],[f393,f499])).

fof(f393,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f231,f239])).

fof(f231,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f497,plain,(
    spl29_11 ),
    inference(avatar_split_clause,[],[f218,f494])).

fof(f218,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f154])).

fof(f154,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f149,f153,f152,f151,f150])).

fof(f150,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f151,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f152,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f153,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f149,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f148])).

fof(f148,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f83])).

fof(f83,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f81,negated_conjecture,(
    ~ ! [X0] :
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f80])).

fof(f80,conjecture,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f492,plain,(
    spl29_10 ),
    inference(avatar_split_clause,[],[f219,f489])).

fof(f219,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f154])).

fof(f487,plain,(
    spl29_9 ),
    inference(avatar_split_clause,[],[f220,f484])).

fof(f220,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f154])).

fof(f482,plain,(
    spl29_8 ),
    inference(avatar_split_clause,[],[f221,f479])).

fof(f221,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f154])).

fof(f477,plain,(
    spl29_5 ),
    inference(avatar_split_clause,[],[f392,f463])).

fof(f392,plain,(
    v1_funct_1(sK3) ),
    inference(definition_unfolding,[],[f222,f228])).

fof(f228,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f154])).

fof(f222,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f154])).

fof(f476,plain,(
    spl29_7 ),
    inference(avatar_split_clause,[],[f391,f473])).

fof(f391,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f223,f228])).

fof(f223,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f154])).

fof(f471,plain,(
    spl29_6 ),
    inference(avatar_split_clause,[],[f390,f468])).

fof(f390,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f224,f228])).

fof(f224,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f154])).

fof(f461,plain,(
    spl29_4 ),
    inference(avatar_split_clause,[],[f226,f458])).

fof(f226,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f154])).

fof(f456,plain,(
    spl29_3 ),
    inference(avatar_split_clause,[],[f227,f453])).

fof(f227,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f154])).

fof(f451,plain,
    ( spl29_1
    | spl29_2 ),
    inference(avatar_split_clause,[],[f389,f447,f443])).

fof(f389,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK3,sK0,sK1) ),
    inference(definition_unfolding,[],[f229,f228])).

fof(f229,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f154])).

fof(f450,plain,
    ( ~ spl29_1
    | ~ spl29_2 ),
    inference(avatar_split_clause,[],[f388,f447,f443])).

fof(f388,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK3,sK0,sK1) ),
    inference(definition_unfolding,[],[f230,f228])).

fof(f230,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:12:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (7776)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.52  % (7752)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (7756)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (7754)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (7760)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (7766)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (7753)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (7775)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (7767)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (7757)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (7778)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (7779)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (7758)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (7759)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (7755)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (7781)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (7772)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (7753)Refutation not found, incomplete strategy% (7753)------------------------------
% 0.22/0.55  % (7753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7781)Refutation not found, incomplete strategy% (7781)------------------------------
% 0.22/0.55  % (7781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (7781)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7781)Memory used [KB]: 1791
% 0.22/0.55  % (7781)Time elapsed: 0.137 s
% 0.22/0.55  % (7781)------------------------------
% 0.22/0.55  % (7781)------------------------------
% 0.22/0.55  % (7761)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (7780)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (7768)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (7753)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (7753)Memory used [KB]: 1791
% 0.22/0.55  % (7753)Time elapsed: 0.111 s
% 0.22/0.55  % (7753)------------------------------
% 0.22/0.55  % (7753)------------------------------
% 0.22/0.55  % (7777)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (7773)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (7770)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (7771)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (7765)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (7764)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (7762)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (7763)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (7769)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (7774)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.59  % (7764)Refutation not found, incomplete strategy% (7764)------------------------------
% 0.22/0.59  % (7764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (7764)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (7764)Memory used [KB]: 10874
% 0.22/0.59  % (7764)Time elapsed: 0.179 s
% 0.22/0.59  % (7764)------------------------------
% 0.22/0.59  % (7764)------------------------------
% 0.22/0.66  % (7752)Refutation not found, incomplete strategy% (7752)------------------------------
% 0.22/0.66  % (7752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.66  % (7752)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.66  
% 0.22/0.66  % (7752)Memory used [KB]: 1791
% 0.22/0.66  % (7752)Time elapsed: 0.227 s
% 0.22/0.66  % (7752)------------------------------
% 0.22/0.66  % (7752)------------------------------
% 0.22/0.68  % (7794)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.54/0.70  % (7793)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.54/0.70  % (7755)Refutation not found, incomplete strategy% (7755)------------------------------
% 2.54/0.70  % (7755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.71  % (7795)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.68/0.72  % (7755)Termination reason: Refutation not found, incomplete strategy
% 2.68/0.72  
% 2.68/0.72  % (7755)Memory used [KB]: 6268
% 2.68/0.72  % (7755)Time elapsed: 0.278 s
% 2.68/0.72  % (7755)------------------------------
% 2.68/0.72  % (7755)------------------------------
% 2.80/0.73  % (7795)Refutation not found, incomplete strategy% (7795)------------------------------
% 2.80/0.73  % (7795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.80/0.73  % (7795)Termination reason: Refutation not found, incomplete strategy
% 2.80/0.73  
% 2.80/0.73  % (7795)Memory used [KB]: 6268
% 2.80/0.74  % (7795)Time elapsed: 0.113 s
% 2.80/0.74  % (7795)------------------------------
% 2.80/0.74  % (7795)------------------------------
% 2.80/0.75  % (7767)Refutation not found, incomplete strategy% (7767)------------------------------
% 2.80/0.75  % (7767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.80/0.75  % (7767)Termination reason: Refutation not found, incomplete strategy
% 2.80/0.75  
% 2.80/0.75  % (7767)Memory used [KB]: 6524
% 2.80/0.75  % (7767)Time elapsed: 0.287 s
% 2.80/0.75  % (7767)------------------------------
% 2.80/0.75  % (7767)------------------------------
% 2.80/0.77  % (7797)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.47/0.82  % (7776)Time limit reached!
% 3.47/0.82  % (7776)------------------------------
% 3.47/0.82  % (7776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.82  % (7776)Termination reason: Time limit
% 3.47/0.82  % (7776)Termination phase: Saturation
% 3.47/0.82  
% 3.47/0.82  % (7776)Memory used [KB]: 12409
% 3.47/0.82  % (7776)Time elapsed: 0.404 s
% 3.47/0.82  % (7776)------------------------------
% 3.47/0.82  % (7776)------------------------------
% 3.47/0.82  % (7754)Time limit reached!
% 3.47/0.82  % (7754)------------------------------
% 3.47/0.82  % (7754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.82  % (7754)Termination reason: Time limit
% 3.47/0.82  
% 3.47/0.82  % (7754)Memory used [KB]: 7036
% 3.47/0.82  % (7754)Time elapsed: 0.404 s
% 3.47/0.82  % (7754)------------------------------
% 3.47/0.82  % (7754)------------------------------
% 3.47/0.85  % (7820)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.47/0.87  % (7827)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.00/0.89  % (7837)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.00/0.92  % (7758)Time limit reached!
% 4.00/0.92  % (7758)------------------------------
% 4.00/0.92  % (7758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.92  % (7758)Termination reason: Time limit
% 4.00/0.92  % (7758)Termination phase: Saturation
% 4.00/0.92  
% 4.00/0.92  % (7758)Memory used [KB]: 14328
% 4.00/0.92  % (7758)Time elapsed: 0.500 s
% 4.00/0.92  % (7758)------------------------------
% 4.00/0.92  % (7758)------------------------------
% 4.00/0.92  % (7865)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.00/0.93  % (7871)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 4.00/0.94  % (7766)Time limit reached!
% 4.00/0.94  % (7766)------------------------------
% 4.00/0.94  % (7766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.00/0.94  % (7766)Termination reason: Time limit
% 4.00/0.94  
% 4.00/0.94  % (7766)Memory used [KB]: 4861
% 4.00/0.94  % (7766)Time elapsed: 0.524 s
% 4.00/0.94  % (7766)------------------------------
% 4.00/0.94  % (7766)------------------------------
% 4.89/1.06  % (7936)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 4.89/1.07  % (7945)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.89/1.08  % (7759)Time limit reached!
% 4.89/1.08  % (7759)------------------------------
% 4.89/1.08  % (7759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.08  % (7759)Termination reason: Time limit
% 4.89/1.08  % (7759)Termination phase: Saturation
% 4.89/1.08  
% 4.89/1.08  % (7759)Memory used [KB]: 7291
% 4.89/1.08  % (7759)Time elapsed: 0.600 s
% 4.89/1.08  % (7759)------------------------------
% 4.89/1.08  % (7759)------------------------------
% 5.83/1.20  % (7977)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 7.57/1.38  % (7837)Time limit reached!
% 7.57/1.38  % (7837)------------------------------
% 7.57/1.38  % (7837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.57/1.38  % (7837)Termination reason: Time limit
% 7.57/1.38  % (7837)Termination phase: Saturation
% 7.57/1.38  
% 7.57/1.38  % (7837)Memory used [KB]: 21875
% 7.57/1.38  % (7837)Time elapsed: 0.600 s
% 7.57/1.38  % (7837)------------------------------
% 7.57/1.38  % (7837)------------------------------
% 8.17/1.42  % (7779)Time limit reached!
% 8.17/1.42  % (7779)------------------------------
% 8.17/1.42  % (7779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.17/1.42  % (7779)Termination reason: Time limit
% 8.17/1.42  
% 8.17/1.42  % (7779)Memory used [KB]: 10618
% 8.17/1.42  % (7779)Time elapsed: 1.007 s
% 8.17/1.42  % (7779)------------------------------
% 8.17/1.42  % (7779)------------------------------
% 8.75/1.52  % (8033)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 8.75/1.54  % (8034)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 10.46/1.71  % (7768)Time limit reached!
% 10.46/1.71  % (7768)------------------------------
% 10.46/1.71  % (7768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.46/1.71  % (7768)Termination reason: Time limit
% 10.46/1.71  % (7768)Termination phase: Saturation
% 10.46/1.71  
% 10.46/1.72  % (7768)Memory used [KB]: 25841
% 10.46/1.72  % (7768)Time elapsed: 1.300 s
% 10.46/1.72  % (7768)------------------------------
% 10.46/1.72  % (7768)------------------------------
% 10.46/1.74  % (7757)Time limit reached!
% 10.46/1.74  % (7757)------------------------------
% 10.46/1.74  % (7757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.46/1.74  % (7757)Termination reason: Time limit
% 10.46/1.74  
% 10.46/1.74  % (7757)Memory used [KB]: 12792
% 10.46/1.74  % (7757)Time elapsed: 1.315 s
% 10.46/1.74  % (7757)------------------------------
% 10.46/1.74  % (7757)------------------------------
% 10.46/1.74  % (7936)Time limit reached!
% 10.46/1.74  % (7936)------------------------------
% 10.46/1.74  % (7936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.46/1.74  % (7936)Termination reason: Time limit
% 10.46/1.74  % (7936)Termination phase: Saturation
% 10.46/1.74  
% 10.46/1.74  % (7936)Memory used [KB]: 15223
% 10.46/1.74  % (7936)Time elapsed: 0.800 s
% 10.46/1.74  % (7936)------------------------------
% 10.46/1.74  % (7936)------------------------------
% 11.24/1.86  % (8035)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.24/1.86  % (8036)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 11.24/1.88  % (8037)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 11.98/1.88  % (8034)Time limit reached!
% 11.98/1.88  % (8034)------------------------------
% 11.98/1.88  % (8034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.98/1.88  % (8034)Termination reason: Time limit
% 11.98/1.88  
% 11.98/1.88  % (8034)Memory used [KB]: 14328
% 11.98/1.88  % (8034)Time elapsed: 0.416 s
% 11.98/1.88  % (8034)------------------------------
% 11.98/1.88  % (8034)------------------------------
% 13.09/2.02  % (8038)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 13.09/2.05  % (7778)Time limit reached!
% 13.09/2.05  % (7778)------------------------------
% 13.09/2.05  % (7778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.09/2.05  % (8036)Refutation not found, incomplete strategy% (8036)------------------------------
% 13.09/2.05  % (8036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.09/2.05  % (8036)Termination reason: Refutation not found, incomplete strategy
% 13.09/2.05  
% 13.09/2.05  % (8036)Memory used [KB]: 6396
% 13.09/2.05  % (8036)Time elapsed: 0.301 s
% 13.09/2.05  % (8036)------------------------------
% 13.09/2.05  % (8036)------------------------------
% 13.09/2.07  % (7778)Termination reason: Time limit
% 13.09/2.07  
% 13.09/2.07  % (7778)Memory used [KB]: 14711
% 13.09/2.07  % (7778)Time elapsed: 1.638 s
% 13.09/2.07  % (7778)------------------------------
% 13.09/2.07  % (7778)------------------------------
% 14.30/2.18  % (8039)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 14.43/2.21  % (8040)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 14.60/2.25  % (7772)Time limit reached!
% 14.60/2.25  % (7772)------------------------------
% 14.60/2.25  % (7772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.60/2.25  % (7772)Termination reason: Time limit
% 14.60/2.25  % (7772)Termination phase: Saturation
% 14.60/2.25  
% 14.60/2.25  % (7772)Memory used [KB]: 28784
% 14.60/2.25  % (7772)Time elapsed: 1.800 s
% 14.60/2.25  % (7772)------------------------------
% 14.60/2.25  % (7772)------------------------------
% 14.60/2.27  % (8037)Time limit reached!
% 14.60/2.27  % (8037)------------------------------
% 14.60/2.27  % (8037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.60/2.27  % (8037)Termination reason: Time limit
% 14.60/2.27  % (8037)Termination phase: Saturation
% 14.60/2.27  
% 14.60/2.27  % (8037)Memory used [KB]: 12792
% 14.60/2.27  % (8037)Time elapsed: 0.500 s
% 14.60/2.27  % (8037)------------------------------
% 14.60/2.27  % (8037)------------------------------
% 15.28/2.32  % (8038)Time limit reached!
% 15.28/2.32  % (8038)------------------------------
% 15.28/2.32  % (8038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.28/2.32  % (8038)Termination reason: Time limit
% 15.28/2.32  
% 15.28/2.32  % (8038)Memory used [KB]: 8443
% 15.28/2.32  % (8038)Time elapsed: 0.411 s
% 15.28/2.32  % (8038)------------------------------
% 15.28/2.32  % (8038)------------------------------
% 15.28/2.37  % (8041)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.87/2.49  % (8040)Time limit reached!
% 16.87/2.49  % (8040)------------------------------
% 16.87/2.49  % (8040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.87/2.49  % (8040)Termination reason: Time limit
% 16.87/2.49  % (8040)Termination phase: Saturation
% 16.87/2.49  
% 16.87/2.49  % (8040)Memory used [KB]: 3454
% 16.87/2.49  % (8040)Time elapsed: 0.400 s
% 16.87/2.49  % (8040)------------------------------
% 16.87/2.49  % (8040)------------------------------
% 17.84/2.68  % (8041)Time limit reached!
% 17.84/2.68  % (8041)------------------------------
% 17.84/2.68  % (8041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.84/2.68  % (8041)Termination reason: Time limit
% 17.84/2.68  
% 17.84/2.68  % (8041)Memory used [KB]: 7036
% 17.84/2.68  % (8041)Time elapsed: 0.411 s
% 17.84/2.68  % (8041)------------------------------
% 17.84/2.68  % (8041)------------------------------
% 24.98/3.51  % (7760)Time limit reached!
% 24.98/3.51  % (7760)------------------------------
% 24.98/3.51  % (7760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.06/3.52  % (7760)Termination reason: Time limit
% 25.06/3.52  % (7760)Termination phase: Saturation
% 25.06/3.52  
% 25.06/3.52  % (7760)Memory used [KB]: 11129
% 25.06/3.52  % (7760)Time elapsed: 3.100 s
% 25.06/3.52  % (7760)------------------------------
% 25.06/3.52  % (7760)------------------------------
% 25.06/3.57  % (7763)Time limit reached!
% 25.06/3.57  % (7763)------------------------------
% 25.06/3.57  % (7763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.06/3.57  % (7763)Termination reason: Time limit
% 25.06/3.57  
% 25.06/3.57  % (7763)Memory used [KB]: 24306
% 25.06/3.57  % (7763)Time elapsed: 3.129 s
% 25.06/3.57  % (7763)------------------------------
% 25.06/3.57  % (7763)------------------------------
% 26.53/3.73  % (7771)Time limit reached!
% 26.53/3.73  % (7771)------------------------------
% 26.53/3.73  % (7771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.53/3.74  % (7771)Termination reason: Time limit
% 26.53/3.74  
% 26.53/3.74  % (7771)Memory used [KB]: 6652
% 26.53/3.74  % (7771)Time elapsed: 3.318 s
% 26.53/3.74  % (7771)------------------------------
% 26.53/3.74  % (7771)------------------------------
% 27.49/3.87  % (7871)Time limit reached!
% 27.49/3.87  % (7871)------------------------------
% 27.49/3.87  % (7871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.49/3.87  % (7871)Termination reason: Time limit
% 27.49/3.87  % (7871)Termination phase: Saturation
% 27.49/3.87  
% 27.49/3.87  % (7871)Memory used [KB]: 13176
% 27.49/3.87  % (7871)Time elapsed: 3.0000 s
% 27.49/3.87  % (7871)------------------------------
% 27.49/3.87  % (7871)------------------------------
% 29.94/4.17  % (7865)Time limit reached!
% 29.94/4.17  % (7865)------------------------------
% 29.94/4.17  % (7865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.94/4.17  % (7865)Termination reason: Time limit
% 29.94/4.17  
% 29.94/4.17  % (7865)Memory used [KB]: 21748
% 29.94/4.17  % (7865)Time elapsed: 3.321 s
% 29.94/4.17  % (7865)------------------------------
% 29.94/4.17  % (7865)------------------------------
% 29.94/4.18  % (7797)Time limit reached!
% 29.94/4.18  % (7797)------------------------------
% 29.94/4.18  % (7797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.94/4.18  % (7797)Termination reason: Time limit
% 29.94/4.18  
% 29.94/4.18  % (7797)Memory used [KB]: 41705
% 29.94/4.18  % (7797)Time elapsed: 3.452 s
% 29.94/4.18  % (7797)------------------------------
% 29.94/4.18  % (7797)------------------------------
% 38.41/5.25  % (7769)Time limit reached!
% 38.41/5.25  % (7769)------------------------------
% 38.41/5.25  % (7769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.41/5.26  % (7769)Termination reason: Time limit
% 38.41/5.26  % (7769)Termination phase: Saturation
% 38.41/5.26  
% 38.41/5.26  % (7769)Memory used [KB]: 34157
% 38.41/5.26  % (7769)Time elapsed: 4.800 s
% 38.41/5.26  % (7769)------------------------------
% 38.41/5.26  % (7769)------------------------------
% 41.89/5.65  % (7794)Refutation found. Thanks to Tanya!
% 41.89/5.65  % SZS status Theorem for theBenchmark
% 41.89/5.65  % SZS output start Proof for theBenchmark
% 41.89/5.65  fof(f57969,plain,(
% 41.89/5.65    $false),
% 41.89/5.65    inference(avatar_sat_refutation,[],[f450,f451,f456,f461,f471,f476,f477,f482,f487,f492,f497,f502,f512,f517,f527,f532,f597,f652,f657,f695,f752,f817,f925,f930,f992,f1704,f1811,f1813,f1830,f2162,f2258,f2342,f2395,f3496,f3652,f3654,f3675,f3721,f3733,f3739,f3760,f3775,f3780,f8815,f8913,f12222,f12417,f12566,f12568,f12680,f12707,f12710,f12770,f12795,f12797,f12915,f12927,f13075,f13078,f14308,f14339,f14426,f14545,f57834,f57842,f57926,f57958,f57968])).
% 41.89/5.65  fof(f57968,plain,(
% 41.89/5.65    ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_23 | ~spl29_82 | ~spl29_98 | ~spl29_379 | spl29_527 | ~spl29_529),
% 41.89/5.65    inference(avatar_contradiction_clause,[],[f57967])).
% 41.89/5.66  fof(f57967,plain,(
% 41.89/5.66    $false | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_23 | ~spl29_82 | ~spl29_98 | ~spl29_379 | spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57966,f6186])).
% 41.89/5.66  fof(f6186,plain,(
% 41.89/5.66    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl29_17 | ~spl29_23)),
% 41.89/5.66    inference(subsumption_resolution,[],[f6169,f526])).
% 41.89/5.66  fof(f526,plain,(
% 41.89/5.66    v1_funct_1(k1_xboole_0) | ~spl29_17),
% 41.89/5.66    inference(avatar_component_clause,[],[f524])).
% 41.89/5.66  fof(f524,plain,(
% 41.89/5.66    spl29_17 <=> v1_funct_1(k1_xboole_0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_17])])).
% 41.89/5.66  fof(f6169,plain,(
% 41.89/5.66    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl29_23),
% 41.89/5.66    inference(resolution,[],[f6166,f573])).
% 41.89/5.66  fof(f573,plain,(
% 41.89/5.66    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 41.89/5.66    inference(forward_demodulation,[],[f397,f395])).
% 41.89/5.66  fof(f395,plain,(
% 41.89/5.66    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 41.89/5.66    inference(definition_unfolding,[],[f236,f387])).
% 41.89/5.66  fof(f387,plain,(
% 41.89/5.66    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 41.89/5.66    inference(definition_unfolding,[],[f243,f235])).
% 41.89/5.66  fof(f235,plain,(
% 41.89/5.66    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f21])).
% 41.89/5.66  fof(f21,axiom,(
% 41.89/5.66    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 41.89/5.66  fof(f243,plain,(
% 41.89/5.66    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 41.89/5.66    inference(cnf_transformation,[],[f26])).
% 41.89/5.66  fof(f26,axiom,(
% 41.89/5.66    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 41.89/5.66  fof(f236,plain,(
% 41.89/5.66    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 41.89/5.66    inference(cnf_transformation,[],[f22])).
% 41.89/5.66  fof(f22,axiom,(
% 41.89/5.66    ! [X0] : k2_subset_1(X0) = X0),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 41.89/5.66  fof(f397,plain,(
% 41.89/5.66    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 41.89/5.66    inference(definition_unfolding,[],[f240,f387])).
% 41.89/5.66  fof(f240,plain,(
% 41.89/5.66    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 41.89/5.66    inference(cnf_transformation,[],[f23])).
% 41.89/5.66  fof(f23,axiom,(
% 41.89/5.66    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 41.89/5.66  fof(f6166,plain,(
% 41.89/5.66    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X3) | v1_funct_2(X3,k1_xboole_0,X2)) ) | ~spl29_23),
% 41.89/5.66    inference(subsumption_resolution,[],[f1595,f1298])).
% 41.89/5.66  fof(f1298,plain,(
% 41.89/5.66    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_partfun1(X3,k1_xboole_0)) ) | ~spl29_23),
% 41.89/5.66    inference(subsumption_resolution,[],[f1297,f614])).
% 41.89/5.66  fof(f614,plain,(
% 41.89/5.66    v1_xboole_0(k1_xboole_0) | ~spl29_23),
% 41.89/5.66    inference(avatar_component_clause,[],[f612])).
% 41.89/5.66  fof(f612,plain,(
% 41.89/5.66    spl29_23 <=> v1_xboole_0(k1_xboole_0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_23])])).
% 41.89/5.66  fof(f1297,plain,(
% 41.89/5.66    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_partfun1(X3,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)) )),
% 41.89/5.66    inference(superposition,[],[f314,f429])).
% 41.89/5.66  fof(f429,plain,(
% 41.89/5.66    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 41.89/5.66    inference(equality_resolution,[],[f346])).
% 41.89/5.66  fof(f346,plain,(
% 41.89/5.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 41.89/5.66    inference(cnf_transformation,[],[f211])).
% 41.89/5.66  fof(f211,plain,(
% 41.89/5.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 41.89/5.66    inference(flattening,[],[f210])).
% 41.89/5.66  fof(f210,plain,(
% 41.89/5.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 41.89/5.66    inference(nnf_transformation,[],[f18])).
% 41.89/5.66  fof(f18,axiom,(
% 41.89/5.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 41.89/5.66  fof(f314,plain,(
% 41.89/5.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0) | ~v1_xboole_0(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f115])).
% 41.89/5.66  fof(f115,plain,(
% 41.89/5.66    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 41.89/5.66    inference(ennf_transformation,[],[f61])).
% 41.89/5.66  fof(f61,axiom,(
% 41.89/5.66    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 41.89/5.66  fof(f1595,plain,(
% 41.89/5.66    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_partfun1(X3,k1_xboole_0) | ~v1_funct_1(X3) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 41.89/5.66    inference(superposition,[],[f358,f429])).
% 41.89/5.66  fof(f358,plain,(
% 41.89/5.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f137])).
% 41.89/5.66  fof(f137,plain,(
% 41.89/5.66    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 41.89/5.66    inference(flattening,[],[f136])).
% 41.89/5.66  fof(f136,plain,(
% 41.89/5.66    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 41.89/5.66    inference(ennf_transformation,[],[f60])).
% 41.89/5.66  fof(f60,axiom,(
% 41.89/5.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 41.89/5.66  fof(f57966,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_82 | ~spl29_98 | ~spl29_379 | spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(forward_demodulation,[],[f57965,f8859])).
% 41.89/5.66  fof(f8859,plain,(
% 41.89/5.66    k1_xboole_0 = u1_struct_0(sK0) | ~spl29_379),
% 41.89/5.66    inference(avatar_component_clause,[],[f8857])).
% 41.89/5.66  fof(f8857,plain,(
% 41.89/5.66    spl29_379 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_379])])).
% 41.89/5.66  fof(f57965,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_82 | ~spl29_98 | spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57964,f496])).
% 41.89/5.66  fof(f496,plain,(
% 41.89/5.66    v2_pre_topc(sK0) | ~spl29_11),
% 41.89/5.66    inference(avatar_component_clause,[],[f494])).
% 41.89/5.66  fof(f494,plain,(
% 41.89/5.66    spl29_11 <=> v2_pre_topc(sK0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_11])])).
% 41.89/5.66  fof(f57964,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_17 | ~spl29_82 | ~spl29_98 | spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57963,f491])).
% 41.89/5.66  fof(f491,plain,(
% 41.89/5.66    l1_pre_topc(sK0) | ~spl29_10),
% 41.89/5.66    inference(avatar_component_clause,[],[f489])).
% 41.89/5.66  fof(f489,plain,(
% 41.89/5.66    spl29_10 <=> l1_pre_topc(sK0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_10])])).
% 41.89/5.66  fof(f57963,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82 | ~spl29_98 | spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57962,f14338])).
% 41.89/5.66  fof(f14338,plain,(
% 41.89/5.66    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl29_529),
% 41.89/5.66    inference(avatar_component_clause,[],[f14336])).
% 41.89/5.66  fof(f14336,plain,(
% 41.89/5.66    spl29_529 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_529])])).
% 41.89/5.66  fof(f57962,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82 | ~spl29_98 | spl29_527)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57960,f2306])).
% 41.89/5.66  fof(f2306,plain,(
% 41.89/5.66    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl29_98),
% 41.89/5.66    inference(avatar_component_clause,[],[f2304])).
% 41.89/5.66  fof(f2304,plain,(
% 41.89/5.66    spl29_98 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_98])])).
% 41.89/5.66  fof(f57960,plain,(
% 41.89/5.66    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82 | spl29_527)),
% 41.89/5.66    inference(resolution,[],[f14306,f13543])).
% 41.89/5.66  fof(f13543,plain,(
% 41.89/5.66    ( ! [X21] : (v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,X21,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13542,f428])).
% 41.89/5.66  fof(f428,plain,(
% 41.89/5.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 41.89/5.66    inference(equality_resolution,[],[f347])).
% 41.89/5.66  fof(f347,plain,(
% 41.89/5.66    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 41.89/5.66    inference(cnf_transformation,[],[f211])).
% 41.89/5.66  fof(f13542,plain,(
% 41.89/5.66    ( ! [X21] : (~v5_pre_topc(k1_xboole_0,X21,sK1) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13541,f237])).
% 41.89/5.66  fof(f237,plain,(
% 41.89/5.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 41.89/5.66    inference(cnf_transformation,[],[f28])).
% 41.89/5.66  fof(f28,axiom,(
% 41.89/5.66    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 41.89/5.66  fof(f13541,plain,(
% 41.89/5.66    ( ! [X21] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,X21,sK1) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13540,f428])).
% 41.89/5.66  fof(f13540,plain,(
% 41.89/5.66    ( ! [X21] : (~v5_pre_topc(k1_xboole_0,X21,sK1) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13539,f526])).
% 41.89/5.66  fof(f13539,plain,(
% 41.89/5.66    ( ! [X21] : (~v1_funct_1(k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X21,sK1) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13538,f428])).
% 41.89/5.66  fof(f13538,plain,(
% 41.89/5.66    ( ! [X21] : (~v5_pre_topc(k1_xboole_0,X21,sK1) | v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13537,f428])).
% 41.89/5.66  fof(f13537,plain,(
% 41.89/5.66    ( ! [X21] : (v5_pre_topc(k1_xboole_0,X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13536,f428])).
% 41.89/5.66  fof(f13536,plain,(
% 41.89/5.66    ( ! [X21] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X21),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13535,f428])).
% 41.89/5.66  fof(f13535,plain,(
% 41.89/5.66    ( ! [X21] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13534,f486])).
% 41.89/5.66  fof(f486,plain,(
% 41.89/5.66    v2_pre_topc(sK1) | ~spl29_9),
% 41.89/5.66    inference(avatar_component_clause,[],[f484])).
% 41.89/5.66  fof(f484,plain,(
% 41.89/5.66    spl29_9 <=> v2_pre_topc(sK1)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_9])])).
% 41.89/5.66  fof(f13534,plain,(
% 41.89/5.66    ( ! [X21] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | (~spl29_8 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13237,f481])).
% 41.89/5.66  fof(f481,plain,(
% 41.89/5.66    l1_pre_topc(sK1) | ~spl29_8),
% 41.89/5.66    inference(avatar_component_clause,[],[f479])).
% 41.89/5.66  fof(f479,plain,(
% 41.89/5.66    spl29_8 <=> l1_pre_topc(sK1)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_8])])).
% 41.89/5.66  fof(f13237,plain,(
% 41.89/5.66    ( ! [X21] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),X21,sK1) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X21),k1_xboole_0),u1_struct_0(X21),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X21) | ~v2_pre_topc(X21)) ) | ~spl29_82),
% 41.89/5.66    inference(superposition,[],[f2090,f1931])).
% 41.89/5.66  fof(f1931,plain,(
% 41.89/5.66    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl29_82),
% 41.89/5.66    inference(avatar_component_clause,[],[f1929])).
% 41.89/5.66  fof(f1929,plain,(
% 41.89/5.66    spl29_82 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_82])])).
% 41.89/5.66  fof(f2090,plain,(
% 41.89/5.66    ( ! [X0,X1] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,X1) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(resolution,[],[f440,f573])).
% 41.89/5.66  fof(f440,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(duplicate_literal_removal,[],[f413])).
% 41.89/5.66  fof(f413,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(equality_resolution,[],[f272])).
% 41.89/5.66  fof(f272,plain,(
% 41.89/5.66    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f160])).
% 41.89/5.66  fof(f160,plain,(
% 41.89/5.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 41.89/5.66    inference(nnf_transformation,[],[f99])).
% 41.89/5.66  fof(f99,plain,(
% 41.89/5.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 41.89/5.66    inference(flattening,[],[f98])).
% 41.89/5.66  fof(f98,plain,(
% 41.89/5.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 41.89/5.66    inference(ennf_transformation,[],[f79])).
% 41.89/5.66  fof(f79,axiom,(
% 41.89/5.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 41.89/5.66  fof(f14306,plain,(
% 41.89/5.66    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl29_527),
% 41.89/5.66    inference(avatar_component_clause,[],[f14305])).
% 41.89/5.66  fof(f14305,plain,(
% 41.89/5.66    spl29_527 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_527])])).
% 41.89/5.66  fof(f57958,plain,(
% 41.89/5.66    spl29_98 | ~spl29_1 | ~spl29_97),
% 41.89/5.66    inference(avatar_split_clause,[],[f57957,f2252,f443,f2304])).
% 41.89/5.66  fof(f443,plain,(
% 41.89/5.66    spl29_1 <=> v5_pre_topc(sK3,sK0,sK1)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_1])])).
% 41.89/5.66  fof(f2252,plain,(
% 41.89/5.66    spl29_97 <=> k1_xboole_0 = sK3),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_97])])).
% 41.89/5.66  fof(f57957,plain,(
% 41.89/5.66    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl29_1 | ~spl29_97)),
% 41.89/5.66    inference(forward_demodulation,[],[f444,f2254])).
% 41.89/5.66  fof(f2254,plain,(
% 41.89/5.66    k1_xboole_0 = sK3 | ~spl29_97),
% 41.89/5.66    inference(avatar_component_clause,[],[f2252])).
% 41.89/5.66  fof(f444,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,sK1) | ~spl29_1),
% 41.89/5.66    inference(avatar_component_clause,[],[f443])).
% 41.89/5.66  fof(f57926,plain,(
% 41.89/5.66    ~spl29_527 | ~spl29_97 | spl29_181),
% 41.89/5.66    inference(avatar_split_clause,[],[f57925,f3693,f2252,f14305])).
% 41.89/5.66  fof(f3693,plain,(
% 41.89/5.66    spl29_181 <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_181])])).
% 41.89/5.66  fof(f57925,plain,(
% 41.89/5.66    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_97 | spl29_181)),
% 41.89/5.66    inference(forward_demodulation,[],[f3694,f2254])).
% 41.89/5.66  fof(f3694,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl29_181),
% 41.89/5.66    inference(avatar_component_clause,[],[f3693])).
% 41.89/5.66  fof(f57842,plain,(
% 41.89/5.66    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_xboole_0 != sK3 | u1_struct_0(sK1) != k2_relat_1(sK3) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 41.89/5.66    introduced(theory_tautology_sat_conflict,[])).
% 41.89/5.66  fof(f57834,plain,(
% 41.89/5.66    ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_23 | ~spl29_82 | spl29_98 | ~spl29_379 | ~spl29_527 | ~spl29_529),
% 41.89/5.66    inference(avatar_contradiction_clause,[],[f57833])).
% 41.89/5.66  fof(f57833,plain,(
% 41.89/5.66    $false | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_23 | ~spl29_82 | spl29_98 | ~spl29_379 | ~spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57832,f6186])).
% 41.89/5.66  fof(f57832,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_23 | ~spl29_82 | spl29_98 | ~spl29_379 | ~spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(forward_demodulation,[],[f57831,f8859])).
% 41.89/5.66  fof(f57831,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_23 | ~spl29_82 | spl29_98 | ~spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57830,f614])).
% 41.89/5.66  fof(f57830,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0) | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_17 | ~spl29_82 | spl29_98 | ~spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57829,f496])).
% 41.89/5.66  fof(f57829,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | ~v1_xboole_0(k1_xboole_0) | (~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_17 | ~spl29_82 | spl29_98 | ~spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57828,f491])).
% 41.89/5.66  fof(f57828,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_xboole_0(k1_xboole_0) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82 | spl29_98 | ~spl29_527 | ~spl29_529)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57827,f14338])).
% 41.89/5.66  fof(f57827,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_xboole_0(k1_xboole_0) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82 | spl29_98 | ~spl29_527)),
% 41.89/5.66    inference(subsumption_resolution,[],[f57814,f2305])).
% 41.89/5.66  fof(f2305,plain,(
% 41.89/5.66    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl29_98),
% 41.89/5.66    inference(avatar_component_clause,[],[f2304])).
% 41.89/5.66  fof(f57814,plain,(
% 41.89/5.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_xboole_0(k1_xboole_0) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82 | ~spl29_527)),
% 41.89/5.66    inference(resolution,[],[f13586,f14317])).
% 41.89/5.66  fof(f14317,plain,(
% 41.89/5.66    ( ! [X0] : (v5_pre_topc(X0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_xboole_0(X0)) ) | ~spl29_527),
% 41.89/5.66    inference(superposition,[],[f14307,f266])).
% 41.89/5.66  fof(f266,plain,(
% 41.89/5.66    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f91])).
% 41.89/5.66  fof(f91,plain,(
% 41.89/5.66    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 41.89/5.66    inference(ennf_transformation,[],[f2])).
% 41.89/5.66  fof(f2,axiom,(
% 41.89/5.66    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 41.89/5.66  fof(f14307,plain,(
% 41.89/5.66    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl29_527),
% 41.89/5.66    inference(avatar_component_clause,[],[f14305])).
% 41.89/5.66  fof(f13586,plain,(
% 41.89/5.66    ( ! [X27] : (~v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,X27,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13585,f428])).
% 41.89/5.66  fof(f13585,plain,(
% 41.89/5.66    ( ! [X27] : (~v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X27,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13584,f237])).
% 41.89/5.66  fof(f13584,plain,(
% 41.89/5.66    ( ! [X27] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X27,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13583,f428])).
% 41.89/5.66  fof(f13583,plain,(
% 41.89/5.66    ( ! [X27] : (~v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X27,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_17 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13582,f526])).
% 41.89/5.66  fof(f13582,plain,(
% 41.89/5.66    ( ! [X27] : (~v1_funct_1(k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X27,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13581,f428])).
% 41.89/5.66  fof(f13581,plain,(
% 41.89/5.66    ( ! [X27] : (~v5_pre_topc(k1_xboole_0,X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X27,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13580,f428])).
% 41.89/5.66  fof(f13580,plain,(
% 41.89/5.66    ( ! [X27] : (v5_pre_topc(k1_xboole_0,X27,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13579,f428])).
% 41.89/5.66  fof(f13579,plain,(
% 41.89/5.66    ( ! [X27] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X27),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(forward_demodulation,[],[f13578,f428])).
% 41.89/5.66  fof(f13578,plain,(
% 41.89/5.66    ( ! [X27] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_9 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13577,f486])).
% 41.89/5.66  fof(f13577,plain,(
% 41.89/5.66    ( ! [X27] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | (~spl29_8 | ~spl29_82)),
% 41.89/5.66    inference(subsumption_resolution,[],[f13242,f481])).
% 41.89/5.66  fof(f13242,plain,(
% 41.89/5.66    ( ! [X27] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),k1_xboole_0) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,sK1) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),X27,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0)) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(sK1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X27),k1_xboole_0),u1_struct_0(X27),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X27) | ~v2_pre_topc(X27)) ) | ~spl29_82),
% 41.89/5.66    inference(superposition,[],[f2124,f1931])).
% 41.89/5.66  fof(f2124,plain,(
% 41.89/5.66    ( ! [X0,X1] : (~v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,X1) | ~v5_pre_topc(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) | ~m1_subset_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))),u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(resolution,[],[f441,f573])).
% 41.89/5.66  fof(f441,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(duplicate_literal_removal,[],[f412])).
% 41.89/5.66  fof(f412,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(equality_resolution,[],[f273])).
% 41.89/5.66  fof(f273,plain,(
% 41.89/5.66    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f160])).
% 41.89/5.66  fof(f14545,plain,(
% 41.89/5.66    spl29_50 | spl29_23),
% 41.89/5.66    inference(avatar_split_clause,[],[f14543,f612,f971])).
% 41.89/5.66  fof(f971,plain,(
% 41.89/5.66    spl29_50 <=> ! [X5] : ~v1_xboole_0(X5)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_50])])).
% 41.89/5.66  fof(f14543,plain,(
% 41.89/5.66    ( ! [X1] : (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X1)) )),
% 41.89/5.66    inference(superposition,[],[f290,f2550])).
% 41.89/5.66  fof(f2550,plain,(
% 41.89/5.66    ( ! [X7] : (k1_xboole_0 = sK12(X7) | ~v1_xboole_0(X7)) )),
% 41.89/5.66    inference(resolution,[],[f962,f284])).
% 41.89/5.66  fof(f284,plain,(
% 41.89/5.66    ( ! [X0] : (r2_hidden(sK9(X0),X0) | k1_xboole_0 = X0) )),
% 41.89/5.66    inference(cnf_transformation,[],[f170])).
% 41.89/5.66  fof(f170,plain,(
% 41.89/5.66    ! [X0] : (r2_hidden(sK9(X0),X0) | k1_xboole_0 = X0)),
% 41.89/5.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f107,f169])).
% 41.89/5.66  fof(f169,plain,(
% 41.89/5.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK9(X0),X0))),
% 41.89/5.66    introduced(choice_axiom,[])).
% 41.89/5.66  fof(f107,plain,(
% 41.89/5.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 41.89/5.66    inference(ennf_transformation,[],[f3])).
% 41.89/5.66  fof(f3,axiom,(
% 41.89/5.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 41.89/5.66  fof(f962,plain,(
% 41.89/5.66    ( ! [X17,X16] : (~r2_hidden(X17,sK12(X16)) | ~v1_xboole_0(X16)) )),
% 41.89/5.66    inference(resolution,[],[f373,f289])).
% 41.89/5.66  fof(f289,plain,(
% 41.89/5.66    ( ! [X0] : (m1_subset_1(sK12(X0),k1_zfmisc_1(X0))) )),
% 41.89/5.66    inference(cnf_transformation,[],[f176])).
% 41.89/5.66  fof(f176,plain,(
% 41.89/5.66    ! [X0] : (v1_xboole_0(sK12(X0)) & m1_subset_1(sK12(X0),k1_zfmisc_1(X0)))),
% 41.89/5.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f25,f175])).
% 41.89/5.66  fof(f175,plain,(
% 41.89/5.66    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK12(X0)) & m1_subset_1(sK12(X0),k1_zfmisc_1(X0))))),
% 41.89/5.66    introduced(choice_axiom,[])).
% 41.89/5.66  fof(f25,axiom,(
% 41.89/5.66    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 41.89/5.66  fof(f373,plain,(
% 41.89/5.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f144])).
% 41.89/5.66  fof(f144,plain,(
% 41.89/5.66    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 41.89/5.66    inference(ennf_transformation,[],[f33])).
% 41.89/5.66  fof(f33,axiom,(
% 41.89/5.66    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 41.89/5.66  fof(f290,plain,(
% 41.89/5.66    ( ! [X0] : (v1_xboole_0(sK12(X0))) )),
% 41.89/5.66    inference(cnf_transformation,[],[f176])).
% 41.89/5.66  fof(f14426,plain,(
% 41.89/5.66    spl29_379 | ~spl29_15 | ~spl29_18 | ~spl29_108),
% 41.89/5.66    inference(avatar_split_clause,[],[f14422,f2354,f529,f514,f8857])).
% 41.89/5.66  fof(f514,plain,(
% 41.89/5.66    spl29_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_15])])).
% 41.89/5.66  fof(f529,plain,(
% 41.89/5.66    spl29_18 <=> v1_relat_1(k1_xboole_0)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_18])])).
% 41.89/5.66  fof(f2354,plain,(
% 41.89/5.66    spl29_108 <=> v1_partfun1(k1_xboole_0,u1_struct_0(sK0))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_108])])).
% 41.89/5.66  fof(f14422,plain,(
% 41.89/5.66    k1_xboole_0 = u1_struct_0(sK0) | (~spl29_15 | ~spl29_18 | ~spl29_108)),
% 41.89/5.66    inference(resolution,[],[f2356,f1437])).
% 41.89/5.66  fof(f1437,plain,(
% 41.89/5.66    ( ! [X0] : (~v1_partfun1(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | (~spl29_15 | ~spl29_18)),
% 41.89/5.66    inference(subsumption_resolution,[],[f1436,f531])).
% 41.89/5.66  fof(f531,plain,(
% 41.89/5.66    v1_relat_1(k1_xboole_0) | ~spl29_18),
% 41.89/5.66    inference(avatar_component_clause,[],[f529])).
% 41.89/5.66  fof(f1436,plain,(
% 41.89/5.66    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl29_15),
% 41.89/5.66    inference(subsumption_resolution,[],[f1420,f911])).
% 41.89/5.66  fof(f911,plain,(
% 41.89/5.66    ( ! [X7] : (v4_relat_1(k1_xboole_0,X7)) )),
% 41.89/5.66    inference(resolution,[],[f353,f237])).
% 41.89/5.66  fof(f353,plain,(
% 41.89/5.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f133])).
% 41.89/5.66  fof(f133,plain,(
% 41.89/5.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 41.89/5.66    inference(ennf_transformation,[],[f52])).
% 41.89/5.66  fof(f52,axiom,(
% 41.89/5.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 41.89/5.66  fof(f1420,plain,(
% 41.89/5.66    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl29_15),
% 41.89/5.66    inference(superposition,[],[f324,f516])).
% 41.89/5.66  fof(f516,plain,(
% 41.89/5.66    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl29_15),
% 41.89/5.66    inference(avatar_component_clause,[],[f514])).
% 41.89/5.66  fof(f324,plain,(
% 41.89/5.66    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f189])).
% 41.89/5.66  fof(f189,plain,(
% 41.89/5.66    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 41.89/5.66    inference(nnf_transformation,[],[f127])).
% 41.89/5.66  fof(f127,plain,(
% 41.89/5.66    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 41.89/5.66    inference(flattening,[],[f126])).
% 41.89/5.66  fof(f126,plain,(
% 41.89/5.66    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 41.89/5.66    inference(ennf_transformation,[],[f65])).
% 41.89/5.66  fof(f65,axiom,(
% 41.89/5.66    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 41.89/5.66  fof(f2356,plain,(
% 41.89/5.66    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | ~spl29_108),
% 41.89/5.66    inference(avatar_component_clause,[],[f2354])).
% 41.89/5.66  fof(f14339,plain,(
% 41.89/5.66    spl29_529 | ~spl29_82 | ~spl29_97 | ~spl29_179),
% 41.89/5.66    inference(avatar_split_clause,[],[f14334,f3685,f2252,f1929,f14336])).
% 41.89/5.66  fof(f3685,plain,(
% 41.89/5.66    spl29_179 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_179])])).
% 41.89/5.66  fof(f14334,plain,(
% 41.89/5.66    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl29_82 | ~spl29_97 | ~spl29_179)),
% 41.89/5.66    inference(forward_demodulation,[],[f14333,f2254])).
% 41.89/5.66  fof(f14333,plain,(
% 41.89/5.66    v1_funct_2(sK3,u1_struct_0(sK0),k1_xboole_0) | (~spl29_82 | ~spl29_179)),
% 41.89/5.66    inference(forward_demodulation,[],[f3686,f1931])).
% 41.89/5.66  fof(f3686,plain,(
% 41.89/5.66    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl29_179),
% 41.89/5.66    inference(avatar_component_clause,[],[f3685])).
% 41.89/5.66  fof(f14308,plain,(
% 41.89/5.66    spl29_527 | ~spl29_97 | ~spl29_181),
% 41.89/5.66    inference(avatar_split_clause,[],[f14303,f3693,f2252,f14305])).
% 41.89/5.66  fof(f14303,plain,(
% 41.89/5.66    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_97 | ~spl29_181)),
% 41.89/5.66    inference(forward_demodulation,[],[f3695,f2254])).
% 41.89/5.66  fof(f3695,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl29_181),
% 41.89/5.66    inference(avatar_component_clause,[],[f3693])).
% 41.89/5.66  fof(f13078,plain,(
% 41.89/5.66    spl29_101 | ~spl29_7 | ~spl29_97),
% 41.89/5.66    inference(avatar_split_clause,[],[f13020,f2252,f473,f2319])).
% 41.89/5.66  fof(f2319,plain,(
% 41.89/5.66    spl29_101 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_101])])).
% 41.89/5.66  fof(f473,plain,(
% 41.89/5.66    spl29_7 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_7])])).
% 41.89/5.66  fof(f13020,plain,(
% 41.89/5.66    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl29_7 | ~spl29_97)),
% 41.89/5.66    inference(superposition,[],[f475,f2254])).
% 41.89/5.66  fof(f475,plain,(
% 41.89/5.66    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl29_7),
% 41.89/5.66    inference(avatar_component_clause,[],[f473])).
% 41.89/5.66  fof(f13075,plain,(
% 41.89/5.66    ~spl29_98 | spl29_1 | ~spl29_97),
% 41.89/5.66    inference(avatar_split_clause,[],[f13014,f2252,f443,f2304])).
% 41.89/5.66  fof(f13014,plain,(
% 41.89/5.66    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl29_1 | ~spl29_97)),
% 41.89/5.66    inference(superposition,[],[f445,f2254])).
% 41.89/5.66  fof(f445,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | spl29_1),
% 41.89/5.66    inference(avatar_component_clause,[],[f443])).
% 41.89/5.66  fof(f12927,plain,(
% 41.89/5.66    ~spl29_25 | ~spl29_179 | ~spl29_181 | spl29_2 | ~spl29_4 | ~spl29_10 | ~spl29_11 | ~spl29_86 | ~spl29_178),
% 41.89/5.66    inference(avatar_split_clause,[],[f12926,f3681,f2021,f494,f489,f458,f447,f3693,f3685,f621])).
% 41.89/5.66  fof(f621,plain,(
% 41.89/5.66    spl29_25 <=> v1_xboole_0(sK3)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_25])])).
% 41.89/5.66  fof(f447,plain,(
% 41.89/5.66    spl29_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_2])])).
% 41.89/5.66  fof(f458,plain,(
% 41.89/5.66    spl29_4 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).
% 41.89/5.66  fof(f2021,plain,(
% 41.89/5.66    spl29_86 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_86])])).
% 41.89/5.66  fof(f3681,plain,(
% 41.89/5.66    spl29_178 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_178])])).
% 41.89/5.66  fof(f12926,plain,(
% 41.89/5.66    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_xboole_0(sK3) | (~spl29_4 | ~spl29_10 | ~spl29_11 | ~spl29_86 | ~spl29_178)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12925,f496])).
% 41.89/5.66  fof(f12925,plain,(
% 41.89/5.66    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~v1_xboole_0(sK3) | (~spl29_4 | ~spl29_10 | ~spl29_86 | ~spl29_178)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12924,f491])).
% 41.89/5.66  fof(f12924,plain,(
% 41.89/5.66    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_xboole_0(sK3) | (~spl29_4 | ~spl29_86 | ~spl29_178)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12923,f3682])).
% 41.89/5.66  fof(f3682,plain,(
% 41.89/5.66    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl29_178),
% 41.89/5.66    inference(avatar_component_clause,[],[f3681])).
% 41.89/5.66  fof(f12923,plain,(
% 41.89/5.66    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_xboole_0(sK3) | (~spl29_4 | ~spl29_86)),
% 41.89/5.66    inference(subsumption_resolution,[],[f10953,f2022])).
% 41.89/5.66  fof(f2022,plain,(
% 41.89/5.66    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl29_86),
% 41.89/5.66    inference(avatar_component_clause,[],[f2021])).
% 41.89/5.66  fof(f10953,plain,(
% 41.89/5.66    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_xboole_0(sK3) | ~spl29_4),
% 41.89/5.66    inference(resolution,[],[f3006,f460])).
% 41.89/5.66  fof(f460,plain,(
% 41.89/5.66    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl29_4),
% 41.89/5.66    inference(avatar_component_clause,[],[f458])).
% 41.89/5.66  fof(f3006,plain,(
% 41.89/5.66    ( ! [X17,X18,X16] : (~v1_funct_2(X16,u1_struct_0(g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17))),u1_struct_0(X18)) | v5_pre_topc(X16,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)),X18) | ~v5_pre_topc(X16,X17,X18) | ~v1_funct_2(X16,u1_struct_0(X17),u1_struct_0(X18)) | ~l1_pre_topc(X18) | ~v2_pre_topc(X18) | ~l1_pre_topc(X17) | ~v2_pre_topc(X17) | ~v1_xboole_0(X16)) )),
% 41.89/5.66    inference(global_subsumption,[],[f2055])).
% 41.89/5.66  fof(f2055,plain,(
% 41.89/5.66    ( ! [X6,X7,X5] : (~v5_pre_topc(X5,X6,X7) | v5_pre_topc(X5,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),X7) | ~v1_funct_2(X5,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))),u1_struct_0(X7)) | ~v1_funct_2(X5,u1_struct_0(X6),u1_struct_0(X7)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | ~v1_xboole_0(X5)) )),
% 41.89/5.66    inference(subsumption_resolution,[],[f2054,f550])).
% 41.89/5.66  fof(f550,plain,(
% 41.89/5.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 41.89/5.66    inference(superposition,[],[f237,f266])).
% 41.89/5.66  fof(f2054,plain,(
% 41.89/5.66    ( ! [X6,X7,X5] : (~v5_pre_topc(X5,X6,X7) | v5_pre_topc(X5,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),X7) | ~v1_funct_2(X5,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))),u1_struct_0(X7)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X5,u1_struct_0(X6),u1_struct_0(X7)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | ~v1_xboole_0(X5)) )),
% 41.89/5.66    inference(subsumption_resolution,[],[f2046,f265])).
% 41.89/5.66  fof(f265,plain,(
% 41.89/5.66    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f90])).
% 41.89/5.66  fof(f90,plain,(
% 41.89/5.66    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 41.89/5.66    inference(ennf_transformation,[],[f47])).
% 41.89/5.66  fof(f47,axiom,(
% 41.89/5.66    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 41.89/5.66  fof(f2046,plain,(
% 41.89/5.66    ( ! [X6,X7,X5] : (~v5_pre_topc(X5,X6,X7) | v5_pre_topc(X5,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)),X7) | ~v1_funct_2(X5,u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))),u1_struct_0(X7)) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))) | ~v1_funct_2(X5,u1_struct_0(X6),u1_struct_0(X7)) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | ~v1_xboole_0(X5)) )),
% 41.89/5.66    inference(resolution,[],[f438,f550])).
% 41.89/5.66  fof(f438,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(duplicate_literal_removal,[],[f415])).
% 41.89/5.66  fof(f415,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(equality_resolution,[],[f274])).
% 41.89/5.66  fof(f274,plain,(
% 41.89/5.66    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f161])).
% 41.89/5.66  fof(f161,plain,(
% 41.89/5.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 41.89/5.66    inference(nnf_transformation,[],[f101])).
% 41.89/5.66  fof(f101,plain,(
% 41.89/5.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 41.89/5.66    inference(flattening,[],[f100])).
% 41.89/5.66  fof(f100,plain,(
% 41.89/5.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 41.89/5.66    inference(ennf_transformation,[],[f78])).
% 41.89/5.66  fof(f78,axiom,(
% 41.89/5.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 41.89/5.66  fof(f12915,plain,(
% 41.89/5.66    ~spl29_2 | ~spl29_179 | ~spl29_180 | spl29_181 | ~spl29_4 | ~spl29_5 | ~spl29_10 | ~spl29_11 | ~spl29_30 | ~spl29_86 | ~spl29_178),
% 41.89/5.66    inference(avatar_split_clause,[],[f12914,f3681,f2021,f692,f494,f489,f463,f458,f3693,f3689,f3685,f447])).
% 41.89/5.66  fof(f3689,plain,(
% 41.89/5.66    spl29_180 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_180])])).
% 41.89/5.66  fof(f463,plain,(
% 41.89/5.66    spl29_5 <=> v1_funct_1(sK3)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_5])])).
% 41.89/5.66  fof(f692,plain,(
% 41.89/5.66    spl29_30 <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_30])])).
% 41.89/5.66  fof(f12914,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_5 | ~spl29_10 | ~spl29_11 | ~spl29_30 | ~spl29_86 | ~spl29_178)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12913,f496])).
% 41.89/5.66  fof(f12913,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_5 | ~spl29_10 | ~spl29_30 | ~spl29_86 | ~spl29_178)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12912,f491])).
% 41.89/5.66  fof(f12912,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_5 | ~spl29_30 | ~spl29_86 | ~spl29_178)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12911,f3682])).
% 41.89/5.66  fof(f12911,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_5 | ~spl29_30 | ~spl29_86)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12910,f2022])).
% 41.89/5.66  fof(f12910,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_5 | ~spl29_30)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12909,f465])).
% 41.89/5.66  fof(f465,plain,(
% 41.89/5.66    v1_funct_1(sK3) | ~spl29_5),
% 41.89/5.66    inference(avatar_component_clause,[],[f463])).
% 41.89/5.66  fof(f12909,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_30)),
% 41.89/5.66    inference(subsumption_resolution,[],[f11227,f460])).
% 41.89/5.66  fof(f11227,plain,(
% 41.89/5.66    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl29_30),
% 41.89/5.66    inference(resolution,[],[f2068,f694])).
% 41.89/5.66  fof(f694,plain,(
% 41.89/5.66    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl29_30),
% 41.89/5.66    inference(avatar_component_clause,[],[f692])).
% 41.89/5.66  fof(f2068,plain,(
% 41.89/5.66    ( ! [X4,X2,X3] : (~r1_tarski(X2,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),u1_struct_0(X4))) | v5_pre_topc(X2,X3,X4) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))),u1_struct_0(X4)) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4)))) | ~v1_funct_2(X2,u1_struct_0(X3),u1_struct_0(X4)) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4)) )),
% 41.89/5.66    inference(resolution,[],[f439,f344])).
% 41.89/5.66  fof(f344,plain,(
% 41.89/5.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f209])).
% 41.89/5.66  fof(f209,plain,(
% 41.89/5.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 41.89/5.66    inference(nnf_transformation,[],[f31])).
% 41.89/5.66  fof(f31,axiom,(
% 41.89/5.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 41.89/5.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 41.89/5.66  fof(f439,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(duplicate_literal_removal,[],[f414])).
% 41.89/5.66  fof(f414,plain,(
% 41.89/5.66    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(equality_resolution,[],[f275])).
% 41.89/5.66  fof(f275,plain,(
% 41.89/5.66    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.66    inference(cnf_transformation,[],[f161])).
% 41.89/5.66  fof(f12797,plain,(
% 41.89/5.66    spl29_175 | ~spl29_79 | ~spl29_5 | ~spl29_176),
% 41.89/5.66    inference(avatar_split_clause,[],[f12796,f3668,f463,f1787,f3664])).
% 41.89/5.66  fof(f3664,plain,(
% 41.89/5.66    spl29_175 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_175])])).
% 41.89/5.66  fof(f1787,plain,(
% 41.89/5.66    spl29_79 <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_79])])).
% 41.89/5.66  fof(f3668,plain,(
% 41.89/5.66    spl29_176 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_176])])).
% 41.89/5.66  fof(f12796,plain,(
% 41.89/5.66    ~v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl29_5 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12248,f465])).
% 41.89/5.66  fof(f12248,plain,(
% 41.89/5.66    ~v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(sK3) | v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl29_176),
% 41.89/5.66    inference(resolution,[],[f3669,f358])).
% 41.89/5.66  fof(f3669,plain,(
% 41.89/5.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl29_176),
% 41.89/5.66    inference(avatar_component_clause,[],[f3668])).
% 41.89/5.66  fof(f12795,plain,(
% 41.89/5.66    ~spl29_175 | spl29_177 | ~spl29_1 | ~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_176),
% 41.89/5.66    inference(avatar_split_clause,[],[f12794,f3668,f494,f489,f484,f479,f473,f468,f463,f443,f3672,f3664])).
% 41.89/5.66  fof(f3672,plain,(
% 41.89/5.66    spl29_177 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_177])])).
% 41.89/5.66  fof(f468,plain,(
% 41.89/5.66    spl29_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_6])])).
% 41.89/5.66  fof(f12794,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12793,f496])).
% 41.89/5.66  fof(f12793,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12792,f491])).
% 41.89/5.66  fof(f12792,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12791,f486])).
% 41.89/5.66  fof(f12791,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12790,f481])).
% 41.89/5.66  fof(f12790,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12789,f475])).
% 41.89/5.66  fof(f12789,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12788,f470])).
% 41.89/5.66  fof(f470,plain,(
% 41.89/5.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl29_6),
% 41.89/5.66    inference(avatar_component_clause,[],[f468])).
% 41.89/5.66  fof(f12788,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12237,f465])).
% 41.89/5.66  fof(f12237,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,sK0,sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl29_176),
% 41.89/5.66    inference(resolution,[],[f3669,f438])).
% 41.89/5.66  fof(f12770,plain,(
% 41.89/5.66    ~spl29_175 | spl29_1 | ~spl29_177 | ~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_176),
% 41.89/5.66    inference(avatar_split_clause,[],[f12769,f3668,f494,f489,f484,f479,f473,f468,f463,f3672,f443,f3664])).
% 41.89/5.66  fof(f12769,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_11 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12768,f496])).
% 41.89/5.66  fof(f12768,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_10 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12767,f491])).
% 41.89/5.66  fof(f12767,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_9 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12766,f486])).
% 41.89/5.66  fof(f12766,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_8 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12765,f481])).
% 41.89/5.66  fof(f12765,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_7 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12764,f475])).
% 41.89/5.66  fof(f12764,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_6 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12763,f470])).
% 41.89/5.66  fof(f12763,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl29_5 | ~spl29_176)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12236,f465])).
% 41.89/5.66  fof(f12236,plain,(
% 41.89/5.66    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,sK0,sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl29_176),
% 41.89/5.66    inference(resolution,[],[f3669,f439])).
% 41.89/5.66  fof(f12710,plain,(
% 41.89/5.66    spl29_61 | spl29_79 | ~spl29_4 | ~spl29_5 | ~spl29_30),
% 41.89/5.66    inference(avatar_split_clause,[],[f12709,f692,f463,f458,f1787,f1226])).
% 41.89/5.66  fof(f1226,plain,(
% 41.89/5.66    spl29_61 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 41.89/5.66    introduced(avatar_definition,[new_symbols(naming,[spl29_61])])).
% 41.89/5.66  fof(f12709,plain,(
% 41.89/5.66    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl29_4 | ~spl29_5 | ~spl29_30)),
% 41.89/5.66    inference(subsumption_resolution,[],[f12708,f460])).
% 41.89/5.66  fof(f12708,plain,(
% 41.89/5.66    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl29_5 | ~spl29_30)),
% 41.89/5.66    inference(subsumption_resolution,[],[f7518,f465])).
% 41.89/5.66  fof(f7518,plain,(
% 41.89/5.66    ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl29_30),
% 41.89/5.66    inference(resolution,[],[f1759,f694])).
% 41.89/5.67  fof(f1759,plain,(
% 41.89/5.67    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_zfmisc_1(X4,X5)) | ~v1_funct_1(X3) | v1_partfun1(X3,X4) | v1_xboole_0(X5) | ~v1_funct_2(X3,X4,X5)) )),
% 41.89/5.67    inference(resolution,[],[f310,f344])).
% 41.89/5.67  fof(f310,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f111])).
% 41.89/5.67  fof(f111,plain,(
% 41.89/5.67    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 41.89/5.67    inference(flattening,[],[f110])).
% 41.89/5.67  fof(f110,plain,(
% 41.89/5.67    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 41.89/5.67    inference(ennf_transformation,[],[f63])).
% 41.89/5.67  fof(f63,axiom,(
% 41.89/5.67    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 41.89/5.67  fof(f12707,plain,(
% 41.89/5.67    spl29_82 | spl29_79 | ~spl29_4 | ~spl29_5 | ~spl29_30),
% 41.89/5.67    inference(avatar_split_clause,[],[f12706,f692,f463,f458,f1787,f1929])).
% 41.89/5.67  fof(f12706,plain,(
% 41.89/5.67    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_5 | ~spl29_30)),
% 41.89/5.67    inference(subsumption_resolution,[],[f12705,f465])).
% 41.89/5.67  fof(f12705,plain,(
% 41.89/5.67    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_1(sK3) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl29_4 | ~spl29_30)),
% 41.89/5.67    inference(subsumption_resolution,[],[f8019,f460])).
% 41.89/5.67  fof(f8019,plain,(
% 41.89/5.67    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl29_30),
% 41.89/5.67    inference(resolution,[],[f1909,f694])).
% 41.89/5.67  fof(f1909,plain,(
% 41.89/5.67    ( ! [X4,X5,X3] : (~r1_tarski(X4,k2_zfmisc_1(X5,X3)) | v1_partfun1(X4,X5) | ~v1_funct_2(X4,X5,X3) | ~v1_funct_1(X4) | k1_xboole_0 = X3) )),
% 41.89/5.67    inference(resolution,[],[f436,f344])).
% 41.89/5.67  fof(f436,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 41.89/5.67    inference(duplicate_literal_removal,[],[f362])).
% 41.89/5.67  fof(f362,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f141])).
% 41.89/5.67  fof(f141,plain,(
% 41.89/5.67    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 41.89/5.67    inference(flattening,[],[f140])).
% 41.89/5.67  fof(f140,plain,(
% 41.89/5.67    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 41.89/5.67    inference(ennf_transformation,[],[f70])).
% 41.89/5.67  fof(f70,axiom,(
% 41.89/5.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 41.89/5.67  fof(f12680,plain,(
% 41.89/5.67    spl29_25 | ~spl29_61 | ~spl29_30),
% 41.89/5.67    inference(avatar_split_clause,[],[f4171,f692,f1226,f621])).
% 41.89/5.67  fof(f4171,plain,(
% 41.89/5.67    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(sK3) | ~spl29_30),
% 41.89/5.67    inference(resolution,[],[f1206,f694])).
% 41.89/5.67  fof(f1206,plain,(
% 41.89/5.67    ( ! [X4,X2,X3] : (~r1_tarski(X2,k2_zfmisc_1(X4,X3)) | ~v1_xboole_0(X3) | v1_xboole_0(X2)) )),
% 41.89/5.67    inference(resolution,[],[f313,f344])).
% 41.89/5.67  fof(f313,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f114])).
% 41.89/5.67  fof(f114,plain,(
% 41.89/5.67    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 41.89/5.67    inference(ennf_transformation,[],[f54])).
% 41.89/5.67  fof(f54,axiom,(
% 41.89/5.67    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 41.89/5.67  fof(f12568,plain,(
% 41.89/5.67    ~spl29_25 | ~spl29_14 | spl29_187),
% 41.89/5.67    inference(avatar_split_clause,[],[f12567,f3772,f509,f621])).
% 41.89/5.67  fof(f509,plain,(
% 41.89/5.67    spl29_14 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_14])])).
% 41.89/5.67  fof(f3772,plain,(
% 41.89/5.67    spl29_187 <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_187])])).
% 41.89/5.67  fof(f12567,plain,(
% 41.89/5.67    ~v1_xboole_0(sK3) | (~spl29_14 | spl29_187)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3783,f568])).
% 41.89/5.67  fof(f568,plain,(
% 41.89/5.67    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 41.89/5.67    inference(superposition,[],[f567,f266])).
% 41.89/5.67  fof(f567,plain,(
% 41.89/5.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 41.89/5.67    inference(forward_demodulation,[],[f533,f395])).
% 41.89/5.67  fof(f533,plain,(
% 41.89/5.67    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0))) )),
% 41.89/5.67    inference(global_subsumption,[],[f237,f417])).
% 41.89/5.67  fof(f417,plain,(
% 41.89/5.67    ( ! [X0] : (r1_tarski(k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 41.89/5.67    inference(equality_resolution,[],[f406])).
% 41.89/5.67  fof(f406,plain,(
% 41.89/5.67    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 41.89/5.67    inference(definition_unfolding,[],[f316,f235])).
% 41.89/5.67  fof(f316,plain,(
% 41.89/5.67    ( ! [X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 41.89/5.67    inference(cnf_transformation,[],[f187])).
% 41.89/5.67  fof(f187,plain,(
% 41.89/5.67    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 41.89/5.67    inference(nnf_transformation,[],[f116])).
% 41.89/5.67  fof(f116,plain,(
% 41.89/5.67    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 41.89/5.67    inference(ennf_transformation,[],[f27])).
% 41.89/5.67  fof(f27,axiom,(
% 41.89/5.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 41.89/5.67  fof(f3783,plain,(
% 41.89/5.67    ~r1_tarski(sK3,u1_struct_0(sK1)) | ~v1_xboole_0(sK3) | (~spl29_14 | spl29_187)),
% 41.89/5.67    inference(superposition,[],[f3774,f553])).
% 41.89/5.67  fof(f553,plain,(
% 41.89/5.67    ( ! [X0] : (k2_relat_1(X0) = X0 | ~v1_xboole_0(X0)) ) | ~spl29_14),
% 41.89/5.67    inference(superposition,[],[f511,f266])).
% 41.89/5.67  fof(f511,plain,(
% 41.89/5.67    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl29_14),
% 41.89/5.67    inference(avatar_component_clause,[],[f509])).
% 41.89/5.67  fof(f3774,plain,(
% 41.89/5.67    ~r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | spl29_187),
% 41.89/5.67    inference(avatar_component_clause,[],[f3772])).
% 41.89/5.67  fof(f12566,plain,(
% 41.89/5.67    ~spl29_25 | spl29_180),
% 41.89/5.67    inference(avatar_split_clause,[],[f3787,f3689,f621])).
% 41.89/5.67  fof(f3787,plain,(
% 41.89/5.67    ~v1_xboole_0(sK3) | spl29_180),
% 41.89/5.67    inference(resolution,[],[f3691,f550])).
% 41.89/5.67  fof(f3691,plain,(
% 41.89/5.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | spl29_180),
% 41.89/5.67    inference(avatar_component_clause,[],[f3689])).
% 41.89/5.67  fof(f12417,plain,(
% 41.89/5.67    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 41.89/5.67    introduced(theory_tautology_sat_conflict,[])).
% 41.89/5.67  fof(f12222,plain,(
% 41.89/5.67    ~spl29_28 | ~spl29_39 | ~spl29_45 | ~spl29_46 | ~spl29_78 | ~spl29_79 | spl29_188),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f12221])).
% 41.89/5.67  fof(f12221,plain,(
% 41.89/5.67    $false | (~spl29_28 | ~spl29_39 | ~spl29_45 | ~spl29_46 | ~spl29_78 | ~spl29_79 | spl29_188)),
% 41.89/5.67    inference(subsumption_resolution,[],[f12220,f929])).
% 41.89/5.67  fof(f929,plain,(
% 41.89/5.67    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl29_46),
% 41.89/5.67    inference(avatar_component_clause,[],[f927])).
% 41.89/5.67  fof(f927,plain,(
% 41.89/5.67    spl29_46 <=> v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_46])])).
% 41.89/5.67  fof(f12220,plain,(
% 41.89/5.67    ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl29_28 | ~spl29_39 | ~spl29_45 | ~spl29_78 | ~spl29_79 | spl29_188)),
% 41.89/5.67    inference(subsumption_resolution,[],[f12194,f1789])).
% 41.89/5.67  fof(f1789,plain,(
% 41.89/5.67    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl29_79),
% 41.89/5.67    inference(avatar_component_clause,[],[f1787])).
% 41.89/5.67  fof(f12194,plain,(
% 41.89/5.67    ~v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl29_28 | ~spl29_39 | ~spl29_45 | ~spl29_78 | spl29_188)),
% 41.89/5.67    inference(resolution,[],[f7790,f3779])).
% 41.89/5.67  fof(f3779,plain,(
% 41.89/5.67    ~r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) | spl29_188),
% 41.89/5.67    inference(avatar_component_clause,[],[f3777])).
% 41.89/5.67  fof(f3777,plain,(
% 41.89/5.67    spl29_188 <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_188])])).
% 41.89/5.67  fof(f7790,plain,(
% 41.89/5.67    ( ! [X5] : (r1_tarski(sK3,k2_zfmisc_1(X5,u1_struct_0(sK1))) | ~v1_partfun1(sK3,X5) | ~v4_relat_1(sK3,X5)) ) | (~spl29_28 | ~spl29_39 | ~spl29_45 | ~spl29_78)),
% 41.89/5.67    inference(superposition,[],[f651,f7767])).
% 41.89/5.67  fof(f7767,plain,(
% 41.89/5.67    ( ! [X17] : (u1_struct_0(sK0) = X17 | ~v1_partfun1(sK3,X17) | ~v4_relat_1(sK3,X17)) ) | (~spl29_39 | ~spl29_45 | ~spl29_78)),
% 41.89/5.67    inference(subsumption_resolution,[],[f7766,f816])).
% 41.89/5.67  fof(f816,plain,(
% 41.89/5.67    v1_relat_1(sK3) | ~spl29_39),
% 41.89/5.67    inference(avatar_component_clause,[],[f814])).
% 41.89/5.67  fof(f814,plain,(
% 41.89/5.67    spl29_39 <=> v1_relat_1(sK3)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_39])])).
% 41.89/5.67  fof(f7766,plain,(
% 41.89/5.67    ( ! [X17] : (u1_struct_0(sK0) = X17 | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X17) | ~v4_relat_1(sK3,X17)) ) | (~spl29_45 | ~spl29_78)),
% 41.89/5.67    inference(subsumption_resolution,[],[f7744,f924])).
% 41.89/5.67  fof(f924,plain,(
% 41.89/5.67    v4_relat_1(sK3,u1_struct_0(sK0)) | ~spl29_45),
% 41.89/5.67    inference(avatar_component_clause,[],[f922])).
% 41.89/5.67  fof(f922,plain,(
% 41.89/5.67    spl29_45 <=> v4_relat_1(sK3,u1_struct_0(sK0))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_45])])).
% 41.89/5.67  fof(f7744,plain,(
% 41.89/5.67    ( ! [X17] : (u1_struct_0(sK0) = X17 | ~v4_relat_1(sK3,u1_struct_0(sK0)) | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X17) | ~v4_relat_1(sK3,X17)) ) | ~spl29_78),
% 41.89/5.67    inference(resolution,[],[f1435,f1781])).
% 41.89/5.67  fof(f1781,plain,(
% 41.89/5.67    v1_partfun1(sK3,u1_struct_0(sK0)) | ~spl29_78),
% 41.89/5.67    inference(avatar_component_clause,[],[f1779])).
% 41.89/5.67  fof(f1779,plain,(
% 41.89/5.67    spl29_78 <=> v1_partfun1(sK3,u1_struct_0(sK0))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_78])])).
% 41.89/5.67  fof(f1435,plain,(
% 41.89/5.67    ( ! [X4,X5,X3] : (~v1_partfun1(X3,X5) | X4 = X5 | ~v4_relat_1(X3,X5) | ~v1_relat_1(X3) | ~v1_partfun1(X3,X4) | ~v4_relat_1(X3,X4)) )),
% 41.89/5.67    inference(duplicate_literal_removal,[],[f1422])).
% 41.89/5.67  fof(f1422,plain,(
% 41.89/5.67    ( ! [X4,X5,X3] : (X4 = X5 | ~v1_partfun1(X3,X5) | ~v4_relat_1(X3,X5) | ~v1_relat_1(X3) | ~v1_partfun1(X3,X4) | ~v4_relat_1(X3,X4) | ~v1_relat_1(X3)) )),
% 41.89/5.67    inference(superposition,[],[f324,f324])).
% 41.89/5.67  fof(f651,plain,(
% 41.89/5.67    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl29_28),
% 41.89/5.67    inference(avatar_component_clause,[],[f649])).
% 41.89/5.67  fof(f649,plain,(
% 41.89/5.67    spl29_28 <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_28])])).
% 41.89/5.67  fof(f8913,plain,(
% 41.89/5.67    ~spl29_23 | ~spl29_101 | spl29_108 | spl29_169),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f8912])).
% 41.89/5.67  fof(f8912,plain,(
% 41.89/5.67    $false | (~spl29_23 | ~spl29_101 | spl29_108 | spl29_169)),
% 41.89/5.67    inference(subsumption_resolution,[],[f8911,f614])).
% 41.89/5.67  fof(f8911,plain,(
% 41.89/5.67    ~v1_xboole_0(k1_xboole_0) | (~spl29_101 | spl29_108 | spl29_169)),
% 41.89/5.67    inference(subsumption_resolution,[],[f8910,f3495])).
% 41.89/5.67  fof(f3495,plain,(
% 41.89/5.67    k1_xboole_0 != u1_struct_0(sK1) | spl29_169),
% 41.89/5.67    inference(avatar_component_clause,[],[f3493])).
% 41.89/5.67  fof(f3493,plain,(
% 41.89/5.67    spl29_169 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_169])])).
% 41.89/5.67  fof(f8910,plain,(
% 41.89/5.67    k1_xboole_0 = u1_struct_0(sK1) | ~v1_xboole_0(k1_xboole_0) | (~spl29_101 | spl29_108)),
% 41.89/5.67    inference(subsumption_resolution,[],[f8892,f2355])).
% 41.89/5.67  fof(f2355,plain,(
% 41.89/5.67    ~v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | spl29_108),
% 41.89/5.67    inference(avatar_component_clause,[],[f2354])).
% 41.89/5.67  fof(f8892,plain,(
% 41.89/5.67    v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK1) | ~v1_xboole_0(k1_xboole_0) | ~spl29_101),
% 41.89/5.67    inference(resolution,[],[f2321,f3012])).
% 41.89/5.67  fof(f3012,plain,(
% 41.89/5.67    ( ! [X19,X17,X18] : (~v1_funct_2(X18,X19,X17) | v1_partfun1(X18,X19) | k1_xboole_0 = X17 | ~v1_xboole_0(X18)) )),
% 41.89/5.67    inference(global_subsumption,[],[f1924])).
% 41.89/5.67  fof(f1924,plain,(
% 41.89/5.67    ( ! [X6,X8,X7] : (k1_xboole_0 = X6 | v1_partfun1(X7,X8) | ~v1_funct_2(X7,X8,X6) | ~v1_xboole_0(X7)) )),
% 41.89/5.67    inference(subsumption_resolution,[],[f1910,f265])).
% 41.89/5.67  fof(f1910,plain,(
% 41.89/5.67    ( ! [X6,X8,X7] : (k1_xboole_0 = X6 | v1_partfun1(X7,X8) | ~v1_funct_2(X7,X8,X6) | ~v1_funct_1(X7) | ~v1_xboole_0(X7)) )),
% 41.89/5.67    inference(resolution,[],[f436,f550])).
% 41.89/5.67  fof(f2321,plain,(
% 41.89/5.67    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl29_101),
% 41.89/5.67    inference(avatar_component_clause,[],[f2319])).
% 41.89/5.67  fof(f8815,plain,(
% 41.89/5.67    ~spl29_7 | ~spl29_39 | ~spl29_45 | ~spl29_46 | ~spl29_78 | ~spl29_79 | spl29_175),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f8814])).
% 41.89/5.67  fof(f8814,plain,(
% 41.89/5.67    $false | (~spl29_7 | ~spl29_39 | ~spl29_45 | ~spl29_46 | ~spl29_78 | ~spl29_79 | spl29_175)),
% 41.89/5.67    inference(subsumption_resolution,[],[f8813,f929])).
% 41.89/5.67  fof(f8813,plain,(
% 41.89/5.67    ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl29_7 | ~spl29_39 | ~spl29_45 | ~spl29_78 | ~spl29_79 | spl29_175)),
% 41.89/5.67    inference(subsumption_resolution,[],[f8807,f1789])).
% 41.89/5.67  fof(f8807,plain,(
% 41.89/5.67    ~v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl29_7 | ~spl29_39 | ~spl29_45 | ~spl29_78 | spl29_175)),
% 41.89/5.67    inference(resolution,[],[f7789,f3666])).
% 41.89/5.67  fof(f3666,plain,(
% 41.89/5.67    ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl29_175),
% 41.89/5.67    inference(avatar_component_clause,[],[f3664])).
% 41.89/5.67  fof(f7789,plain,(
% 41.89/5.67    ( ! [X4] : (v1_funct_2(sK3,X4,u1_struct_0(sK1)) | ~v1_partfun1(sK3,X4) | ~v4_relat_1(sK3,X4)) ) | (~spl29_7 | ~spl29_39 | ~spl29_45 | ~spl29_78)),
% 41.89/5.67    inference(superposition,[],[f475,f7767])).
% 41.89/5.67  fof(f3780,plain,(
% 41.89/5.67    ~spl29_188 | spl29_176),
% 41.89/5.67    inference(avatar_split_clause,[],[f3766,f3668,f3777])).
% 41.89/5.67  fof(f3766,plain,(
% 41.89/5.67    ~r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))) | spl29_176),
% 41.89/5.67    inference(resolution,[],[f3670,f344])).
% 41.89/5.67  fof(f3670,plain,(
% 41.89/5.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl29_176),
% 41.89/5.67    inference(avatar_component_clause,[],[f3668])).
% 41.89/5.67  fof(f3775,plain,(
% 41.89/5.67    ~spl29_187 | ~spl29_3 | spl29_176),
% 41.89/5.67    inference(avatar_split_clause,[],[f3765,f3668,f453,f3772])).
% 41.89/5.67  fof(f453,plain,(
% 41.89/5.67    spl29_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_3])])).
% 41.89/5.67  fof(f3765,plain,(
% 41.89/5.67    ~r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | (~spl29_3 | spl29_176)),
% 41.89/5.67    inference(resolution,[],[f3670,f1672])).
% 41.89/5.67  fof(f1672,plain,(
% 41.89/5.67    ( ! [X17] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X17))) | ~r1_tarski(k2_relat_1(sK3),X17)) ) | ~spl29_3),
% 41.89/5.67    inference(resolution,[],[f376,f455])).
% 41.89/5.67  fof(f455,plain,(
% 41.89/5.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl29_3),
% 41.89/5.67    inference(avatar_component_clause,[],[f453])).
% 41.89/5.67  fof(f376,plain,(
% 41.89/5.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 41.89/5.67    inference(cnf_transformation,[],[f147])).
% 41.89/5.67  fof(f147,plain,(
% 41.89/5.67    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 41.89/5.67    inference(flattening,[],[f146])).
% 41.89/5.67  fof(f146,plain,(
% 41.89/5.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 41.89/5.67    inference(ennf_transformation,[],[f57])).
% 41.89/5.67  fof(f57,axiom,(
% 41.89/5.67    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 41.89/5.67  fof(f3760,plain,(
% 41.89/5.67    ~spl29_186 | ~spl29_5 | ~spl29_6 | ~spl29_78 | spl29_179),
% 41.89/5.67    inference(avatar_split_clause,[],[f3755,f3685,f1779,f468,f463,f3757])).
% 41.89/5.67  fof(f3757,plain,(
% 41.89/5.67    spl29_186 <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_186])])).
% 41.89/5.67  fof(f3755,plain,(
% 41.89/5.67    ~r1_tarski(k2_relat_1(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl29_5 | ~spl29_6 | ~spl29_78 | spl29_179)),
% 41.89/5.67    inference(resolution,[],[f3687,f2214])).
% 41.89/5.67  fof(f2214,plain,(
% 41.89/5.67    ( ! [X11] : (v1_funct_2(sK3,u1_struct_0(sK0),X11) | ~r1_tarski(k2_relat_1(sK3),X11)) ) | (~spl29_5 | ~spl29_6 | ~spl29_78)),
% 41.89/5.67    inference(subsumption_resolution,[],[f2213,f465])).
% 41.89/5.67  fof(f2213,plain,(
% 41.89/5.67    ( ! [X11] : (~r1_tarski(k2_relat_1(sK3),X11) | ~v1_funct_1(sK3) | v1_funct_2(sK3,u1_struct_0(sK0),X11)) ) | (~spl29_6 | ~spl29_78)),
% 41.89/5.67    inference(subsumption_resolution,[],[f2188,f1781])).
% 41.89/5.67  fof(f2188,plain,(
% 41.89/5.67    ( ! [X11] : (~r1_tarski(k2_relat_1(sK3),X11) | ~v1_partfun1(sK3,u1_struct_0(sK0)) | ~v1_funct_1(sK3) | v1_funct_2(sK3,u1_struct_0(sK0),X11)) ) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f1671,f358])).
% 41.89/5.67  fof(f1671,plain,(
% 41.89/5.67    ( ! [X16] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X16))) | ~r1_tarski(k2_relat_1(sK3),X16)) ) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f376,f470])).
% 41.89/5.67  fof(f3687,plain,(
% 41.89/5.67    ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl29_179),
% 41.89/5.67    inference(avatar_component_clause,[],[f3685])).
% 41.89/5.67  fof(f3739,plain,(
% 41.89/5.67    ~spl29_8 | ~spl29_9 | spl29_178),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f3738])).
% 41.89/5.67  fof(f3738,plain,(
% 41.89/5.67    $false | (~spl29_8 | ~spl29_9 | spl29_178)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3737,f486])).
% 41.89/5.67  fof(f3737,plain,(
% 41.89/5.67    ~v2_pre_topc(sK1) | (~spl29_8 | spl29_178)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3735,f481])).
% 41.89/5.67  fof(f3735,plain,(
% 41.89/5.67    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl29_178),
% 41.89/5.67    inference(resolution,[],[f3683,f270])).
% 41.89/5.67  fof(f270,plain,(
% 41.89/5.67    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f95])).
% 41.89/5.67  fof(f95,plain,(
% 41.89/5.67    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 41.89/5.67    inference(flattening,[],[f94])).
% 41.89/5.67  fof(f94,plain,(
% 41.89/5.67    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 41.89/5.67    inference(ennf_transformation,[],[f76])).
% 41.89/5.67  fof(f76,axiom,(
% 41.89/5.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 41.89/5.67  fof(f3683,plain,(
% 41.89/5.67    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl29_178),
% 41.89/5.67    inference(avatar_component_clause,[],[f3681])).
% 41.89/5.67  fof(f3733,plain,(
% 41.89/5.67    ~spl29_10 | ~spl29_11 | spl29_174),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f3732])).
% 41.89/5.67  fof(f3732,plain,(
% 41.89/5.67    $false | (~spl29_10 | ~spl29_11 | spl29_174)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3731,f496])).
% 41.89/5.67  fof(f3731,plain,(
% 41.89/5.67    ~v2_pre_topc(sK0) | (~spl29_10 | spl29_174)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3729,f491])).
% 41.89/5.67  fof(f3729,plain,(
% 41.89/5.67    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl29_174),
% 41.89/5.67    inference(resolution,[],[f3662,f270])).
% 41.89/5.67  fof(f3662,plain,(
% 41.89/5.67    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl29_174),
% 41.89/5.67    inference(avatar_component_clause,[],[f3660])).
% 41.89/5.67  fof(f3660,plain,(
% 41.89/5.67    spl29_174 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_174])])).
% 41.89/5.67  fof(f3721,plain,(
% 41.89/5.67    ~spl29_174 | ~spl29_85 | ~spl29_175 | ~spl29_176 | spl29_2 | ~spl29_177 | ~spl29_3 | ~spl29_4 | ~spl29_5 | ~spl29_8 | ~spl29_9),
% 41.89/5.67    inference(avatar_split_clause,[],[f3720,f484,f479,f463,f458,f453,f3672,f447,f3668,f3664,f2017,f3660])).
% 41.89/5.67  fof(f2017,plain,(
% 41.89/5.67    spl29_85 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_85])])).
% 41.89/5.67  fof(f3720,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4 | ~spl29_5 | ~spl29_8 | ~spl29_9)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3719,f486])).
% 41.89/5.67  fof(f3719,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4 | ~spl29_5 | ~spl29_8)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3718,f481])).
% 41.89/5.67  fof(f3718,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4 | ~spl29_5)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3717,f465])).
% 41.89/5.67  fof(f3717,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4)),
% 41.89/5.67    inference(subsumption_resolution,[],[f2095,f460])).
% 41.89/5.67  fof(f2095,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl29_3),
% 41.89/5.67    inference(resolution,[],[f440,f455])).
% 41.89/5.67  fof(f3675,plain,(
% 41.89/5.67    ~spl29_174 | ~spl29_85 | ~spl29_175 | ~spl29_176 | spl29_177 | ~spl29_2 | ~spl29_3 | ~spl29_4 | ~spl29_5 | ~spl29_8 | ~spl29_9),
% 41.89/5.67    inference(avatar_split_clause,[],[f3658,f484,f479,f463,f458,f453,f447,f3672,f3668,f3664,f2017,f3660])).
% 41.89/5.67  fof(f3658,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4 | ~spl29_5 | ~spl29_8 | ~spl29_9)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3657,f486])).
% 41.89/5.67  fof(f3657,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4 | ~spl29_5 | ~spl29_8)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3656,f481])).
% 41.89/5.67  fof(f3656,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4 | ~spl29_5)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3655,f465])).
% 41.89/5.67  fof(f3655,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl29_3 | ~spl29_4)),
% 41.89/5.67    inference(subsumption_resolution,[],[f2129,f460])).
% 41.89/5.67  fof(f2129,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl29_3),
% 41.89/5.67    inference(resolution,[],[f441,f455])).
% 41.89/5.67  fof(f3654,plain,(
% 41.89/5.67    ~spl29_8 | spl29_86),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f3653])).
% 41.89/5.67  fof(f3653,plain,(
% 41.89/5.67    $false | (~spl29_8 | spl29_86)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3648,f481])).
% 41.89/5.67  fof(f3648,plain,(
% 41.89/5.67    ~l1_pre_topc(sK1) | spl29_86),
% 41.89/5.67    inference(resolution,[],[f887,f2023])).
% 41.89/5.67  fof(f2023,plain,(
% 41.89/5.67    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl29_86),
% 41.89/5.67    inference(avatar_component_clause,[],[f2021])).
% 41.89/5.67  fof(f887,plain,(
% 41.89/5.67    ( ! [X6] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))) | ~l1_pre_topc(X6)) )),
% 41.89/5.67    inference(resolution,[],[f318,f256])).
% 41.89/5.67  fof(f256,plain,(
% 41.89/5.67    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f84])).
% 41.89/5.67  fof(f84,plain,(
% 41.89/5.67    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 41.89/5.67    inference(ennf_transformation,[],[f75])).
% 41.89/5.67  fof(f75,axiom,(
% 41.89/5.67    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 41.89/5.67  fof(f318,plain,(
% 41.89/5.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 41.89/5.67    inference(cnf_transformation,[],[f117])).
% 41.89/5.67  fof(f117,plain,(
% 41.89/5.67    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 41.89/5.67    inference(ennf_transformation,[],[f74])).
% 41.89/5.67  fof(f74,axiom,(
% 41.89/5.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 41.89/5.67  fof(f3652,plain,(
% 41.89/5.67    ~spl29_10 | spl29_85),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f3651])).
% 41.89/5.67  fof(f3651,plain,(
% 41.89/5.67    $false | (~spl29_10 | spl29_85)),
% 41.89/5.67    inference(subsumption_resolution,[],[f3647,f491])).
% 41.89/5.67  fof(f3647,plain,(
% 41.89/5.67    ~l1_pre_topc(sK0) | spl29_85),
% 41.89/5.67    inference(resolution,[],[f887,f2019])).
% 41.89/5.67  fof(f2019,plain,(
% 41.89/5.67    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl29_85),
% 41.89/5.67    inference(avatar_component_clause,[],[f2017])).
% 41.89/5.67  fof(f3496,plain,(
% 41.89/5.67    ~spl29_169 | ~spl29_14 | spl29_105),
% 41.89/5.67    inference(avatar_split_clause,[],[f3491,f2339,f509,f3493])).
% 41.89/5.67  fof(f2339,plain,(
% 41.89/5.67    spl29_105 <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_105])])).
% 41.89/5.67  fof(f3491,plain,(
% 41.89/5.67    k1_xboole_0 != u1_struct_0(sK1) | (~spl29_14 | spl29_105)),
% 41.89/5.67    inference(forward_demodulation,[],[f3490,f511])).
% 41.89/5.67  fof(f3490,plain,(
% 41.89/5.67    k2_relat_1(k1_xboole_0) != u1_struct_0(sK1) | spl29_105),
% 41.89/5.67    inference(subsumption_resolution,[],[f3489,f237])).
% 41.89/5.67  fof(f3489,plain,(
% 41.89/5.67    k2_relat_1(k1_xboole_0) != u1_struct_0(sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl29_105),
% 41.89/5.67    inference(superposition,[],[f2341,f352])).
% 41.89/5.67  fof(f352,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 41.89/5.67    inference(cnf_transformation,[],[f132])).
% 41.89/5.67  fof(f132,plain,(
% 41.89/5.67    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 41.89/5.67    inference(ennf_transformation,[],[f55])).
% 41.89/5.67  fof(f55,axiom,(
% 41.89/5.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 41.89/5.67  fof(f2341,plain,(
% 41.89/5.67    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0) | spl29_105),
% 41.89/5.67    inference(avatar_component_clause,[],[f2339])).
% 41.89/5.67  fof(f2395,plain,(
% 41.89/5.67    ~spl29_25 | spl29_97),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f2392])).
% 41.89/5.67  fof(f2392,plain,(
% 41.89/5.67    $false | (~spl29_25 | spl29_97)),
% 41.89/5.67    inference(unit_resulting_resolution,[],[f623,f2253,f266])).
% 41.89/5.67  fof(f2253,plain,(
% 41.89/5.67    k1_xboole_0 != sK3 | spl29_97),
% 41.89/5.67    inference(avatar_component_clause,[],[f2252])).
% 41.89/5.67  fof(f623,plain,(
% 41.89/5.67    v1_xboole_0(sK3) | ~spl29_25),
% 41.89/5.67    inference(avatar_component_clause,[],[f621])).
% 41.89/5.67  fof(f2342,plain,(
% 41.89/5.67    ~spl29_105 | spl29_71 | ~spl29_97),
% 41.89/5.67    inference(avatar_split_clause,[],[f2292,f2252,f1697,f2339])).
% 41.89/5.67  fof(f1697,plain,(
% 41.89/5.67    spl29_71 <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_71])])).
% 41.89/5.67  fof(f2292,plain,(
% 41.89/5.67    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0) | (spl29_71 | ~spl29_97)),
% 41.89/5.67    inference(superposition,[],[f1698,f2254])).
% 41.89/5.67  fof(f1698,plain,(
% 41.89/5.67    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) | spl29_71),
% 41.89/5.67    inference(avatar_component_clause,[],[f1697])).
% 41.89/5.67  fof(f2258,plain,(
% 41.89/5.67    k1_xboole_0 != sK3 | k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != sK13(k1_xboole_0) | r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~r1_tarski(sK13(k1_xboole_0),k1_xboole_0)),
% 41.89/5.67    introduced(theory_tautology_sat_conflict,[])).
% 41.89/5.67  fof(f2162,plain,(
% 41.89/5.67    spl29_77 | ~spl29_6 | ~spl29_71),
% 41.89/5.67    inference(avatar_split_clause,[],[f2161,f1697,f468,f1753])).
% 41.89/5.67  fof(f1753,plain,(
% 41.89/5.67    spl29_77 <=> u1_struct_0(sK1) = k2_relat_1(sK3)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_77])])).
% 41.89/5.67  fof(f2161,plain,(
% 41.89/5.67    u1_struct_0(sK1) = k2_relat_1(sK3) | (~spl29_6 | ~spl29_71)),
% 41.89/5.67    inference(subsumption_resolution,[],[f2147,f470])).
% 41.89/5.67  fof(f2147,plain,(
% 41.89/5.67    u1_struct_0(sK1) = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl29_71),
% 41.89/5.67    inference(superposition,[],[f1699,f352])).
% 41.89/5.67  fof(f1699,plain,(
% 41.89/5.67    u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) | ~spl29_71),
% 41.89/5.67    inference(avatar_component_clause,[],[f1697])).
% 41.89/5.67  fof(f1830,plain,(
% 41.89/5.67    ~spl29_60 | ~spl29_6 | spl29_25),
% 41.89/5.67    inference(avatar_split_clause,[],[f1218,f621,f468,f1220])).
% 41.89/5.67  fof(f1220,plain,(
% 41.89/5.67    spl29_60 <=> v1_xboole_0(u1_struct_0(sK1))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_60])])).
% 41.89/5.67  fof(f1218,plain,(
% 41.89/5.67    ~v1_xboole_0(u1_struct_0(sK1)) | (~spl29_6 | spl29_25)),
% 41.89/5.67    inference(subsumption_resolution,[],[f1210,f622])).
% 41.89/5.67  fof(f622,plain,(
% 41.89/5.67    ~v1_xboole_0(sK3) | spl29_25),
% 41.89/5.67    inference(avatar_component_clause,[],[f621])).
% 41.89/5.67  fof(f1210,plain,(
% 41.89/5.67    v1_xboole_0(sK3) | ~v1_xboole_0(u1_struct_0(sK1)) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f313,f470])).
% 41.89/5.67  fof(f1813,plain,(
% 41.89/5.67    spl29_78 | ~spl29_5 | ~spl29_6 | ~spl29_7 | spl29_60),
% 41.89/5.67    inference(avatar_split_clause,[],[f1777,f1220,f473,f468,f463,f1779])).
% 41.89/5.67  fof(f1777,plain,(
% 41.89/5.67    v1_partfun1(sK3,u1_struct_0(sK0)) | (~spl29_5 | ~spl29_6 | ~spl29_7 | spl29_60)),
% 41.89/5.67    inference(subsumption_resolution,[],[f1776,f1222])).
% 41.89/5.67  fof(f1222,plain,(
% 41.89/5.67    ~v1_xboole_0(u1_struct_0(sK1)) | spl29_60),
% 41.89/5.67    inference(avatar_component_clause,[],[f1220])).
% 41.89/5.67  fof(f1776,plain,(
% 41.89/5.67    v1_partfun1(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl29_5 | ~spl29_6 | ~spl29_7)),
% 41.89/5.67    inference(subsumption_resolution,[],[f1775,f465])).
% 41.89/5.67  fof(f1775,plain,(
% 41.89/5.67    ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | (~spl29_6 | ~spl29_7)),
% 41.89/5.67    inference(subsumption_resolution,[],[f1763,f475])).
% 41.89/5.67  fof(f1763,plain,(
% 41.89/5.67    ~v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f310,f470])).
% 41.89/5.67  fof(f1811,plain,(
% 41.89/5.67    ~spl29_60 | ~spl29_12 | spl29_72),
% 41.89/5.67    inference(avatar_split_clause,[],[f1801,f1701,f499,f1220])).
% 41.89/5.67  fof(f499,plain,(
% 41.89/5.67    spl29_12 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_12])])).
% 41.89/5.67  fof(f1701,plain,(
% 41.89/5.67    spl29_72 <=> r1_tarski(k6_partfun1(u1_struct_0(sK1)),sK3)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_72])])).
% 41.89/5.67  fof(f1801,plain,(
% 41.89/5.67    ~v1_xboole_0(u1_struct_0(sK1)) | (~spl29_12 | spl29_72)),
% 41.89/5.67    inference(subsumption_resolution,[],[f1717,f568])).
% 41.89/5.67  fof(f1717,plain,(
% 41.89/5.67    ~r1_tarski(u1_struct_0(sK1),sK3) | ~v1_xboole_0(u1_struct_0(sK1)) | (~spl29_12 | spl29_72)),
% 41.89/5.67    inference(superposition,[],[f1703,f552])).
% 41.89/5.67  fof(f552,plain,(
% 41.89/5.67    ( ! [X0] : (k6_partfun1(X0) = X0 | ~v1_xboole_0(X0)) ) | ~spl29_12),
% 41.89/5.67    inference(superposition,[],[f501,f266])).
% 41.89/5.67  fof(f501,plain,(
% 41.89/5.67    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl29_12),
% 41.89/5.67    inference(avatar_component_clause,[],[f499])).
% 41.89/5.67  fof(f1703,plain,(
% 41.89/5.67    ~r1_tarski(k6_partfun1(u1_struct_0(sK1)),sK3) | spl29_72),
% 41.89/5.67    inference(avatar_component_clause,[],[f1701])).
% 41.89/5.67  fof(f1704,plain,(
% 41.89/5.67    spl29_71 | ~spl29_72 | ~spl29_6),
% 41.89/5.67    inference(avatar_split_clause,[],[f1687,f468,f1701,f1697])).
% 41.89/5.67  fof(f1687,plain,(
% 41.89/5.67    ~r1_tarski(k6_partfun1(u1_struct_0(sK1)),sK3) | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f410,f470])).
% 41.89/5.67  fof(f410,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k6_partfun1(X1),X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 41.89/5.67    inference(definition_unfolding,[],[f356,f239])).
% 41.89/5.67  fof(f239,plain,(
% 41.89/5.67    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f69])).
% 41.89/5.67  fof(f69,axiom,(
% 41.89/5.67    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 41.89/5.67  fof(f356,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 41.89/5.67    inference(cnf_transformation,[],[f135])).
% 41.89/5.67  fof(f135,plain,(
% 41.89/5.67    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2))) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 41.89/5.67    inference(flattening,[],[f134])).
% 41.89/5.67  fof(f134,plain,(
% 41.89/5.67    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2))) | ~r1_tarski(k6_relat_1(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 41.89/5.67    inference(ennf_transformation,[],[f58])).
% 41.89/5.67  fof(f58,axiom,(
% 41.89/5.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X1),X2) => (k2_relset_1(X0,X1,X2) = X1 & r1_tarski(X1,k1_relset_1(X0,X1,X2)))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).
% 41.89/5.67  fof(f992,plain,(
% 41.89/5.67    ~spl29_50),
% 41.89/5.67    inference(avatar_contradiction_clause,[],[f989])).
% 41.89/5.67  fof(f989,plain,(
% 41.89/5.67    $false | ~spl29_50),
% 41.89/5.67    inference(subsumption_resolution,[],[f290,f972])).
% 41.89/5.67  fof(f972,plain,(
% 41.89/5.67    ( ! [X5] : (~v1_xboole_0(X5)) ) | ~spl29_50),
% 41.89/5.67    inference(avatar_component_clause,[],[f971])).
% 41.89/5.67  fof(f930,plain,(
% 41.89/5.67    spl29_46 | ~spl29_3),
% 41.89/5.67    inference(avatar_split_clause,[],[f914,f453,f927])).
% 41.89/5.67  fof(f914,plain,(
% 41.89/5.67    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl29_3),
% 41.89/5.67    inference(resolution,[],[f353,f455])).
% 41.89/5.67  fof(f925,plain,(
% 41.89/5.67    spl29_45 | ~spl29_6),
% 41.89/5.67    inference(avatar_split_clause,[],[f913,f468,f922])).
% 41.89/5.67  fof(f913,plain,(
% 41.89/5.67    v4_relat_1(sK3,u1_struct_0(sK0)) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f353,f470])).
% 41.89/5.67  fof(f817,plain,(
% 41.89/5.67    spl29_39 | ~spl29_6),
% 41.89/5.67    inference(avatar_split_clause,[],[f805,f468,f814])).
% 41.89/5.67  fof(f805,plain,(
% 41.89/5.67    v1_relat_1(sK3) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f351,f470])).
% 41.89/5.67  fof(f351,plain,(
% 41.89/5.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f131])).
% 41.89/5.67  fof(f131,plain,(
% 41.89/5.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 41.89/5.67    inference(ennf_transformation,[],[f51])).
% 41.89/5.67  fof(f51,axiom,(
% 41.89/5.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 41.89/5.67  fof(f752,plain,(
% 41.89/5.67    spl29_35 | ~spl29_29),
% 41.89/5.67    inference(avatar_split_clause,[],[f746,f654,f749])).
% 41.89/5.67  fof(f749,plain,(
% 41.89/5.67    spl29_35 <=> k1_xboole_0 = sK13(k1_xboole_0)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_35])])).
% 41.89/5.67  fof(f654,plain,(
% 41.89/5.67    spl29_29 <=> r1_tarski(sK13(k1_xboole_0),k1_xboole_0)),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_29])])).
% 41.89/5.67  fof(f746,plain,(
% 41.89/5.67    k1_xboole_0 = sK13(k1_xboole_0) | ~spl29_29),
% 41.89/5.67    inference(resolution,[],[f656,f268])).
% 41.89/5.67  fof(f268,plain,(
% 41.89/5.67    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 41.89/5.67    inference(cnf_transformation,[],[f93])).
% 41.89/5.67  fof(f93,plain,(
% 41.89/5.67    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 41.89/5.67    inference(ennf_transformation,[],[f6])).
% 41.89/5.67  fof(f6,axiom,(
% 41.89/5.67    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 41.89/5.67  fof(f656,plain,(
% 41.89/5.67    r1_tarski(sK13(k1_xboole_0),k1_xboole_0) | ~spl29_29),
% 41.89/5.67    inference(avatar_component_clause,[],[f654])).
% 41.89/5.67  fof(f695,plain,(
% 41.89/5.67    spl29_30 | ~spl29_3),
% 41.89/5.67    inference(avatar_split_clause,[],[f689,f453,f692])).
% 41.89/5.67  fof(f689,plain,(
% 41.89/5.67    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl29_3),
% 41.89/5.67    inference(resolution,[],[f455,f343])).
% 41.89/5.67  fof(f343,plain,(
% 41.89/5.67    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 41.89/5.67    inference(cnf_transformation,[],[f209])).
% 41.89/5.67  fof(f657,plain,(
% 41.89/5.67    spl29_29 | ~spl29_21),
% 41.89/5.67    inference(avatar_split_clause,[],[f645,f593,f654])).
% 41.89/5.67  fof(f593,plain,(
% 41.89/5.67    spl29_21 <=> m1_subset_1(sK13(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 41.89/5.67    introduced(avatar_definition,[new_symbols(naming,[spl29_21])])).
% 41.89/5.67  fof(f645,plain,(
% 41.89/5.67    r1_tarski(sK13(k1_xboole_0),k1_xboole_0) | ~spl29_21),
% 41.89/5.67    inference(resolution,[],[f343,f595])).
% 41.89/5.67  fof(f595,plain,(
% 41.89/5.67    m1_subset_1(sK13(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl29_21),
% 41.89/5.67    inference(avatar_component_clause,[],[f593])).
% 41.89/5.67  fof(f652,plain,(
% 41.89/5.67    spl29_28 | ~spl29_6),
% 41.89/5.67    inference(avatar_split_clause,[],[f642,f468,f649])).
% 41.89/5.67  fof(f642,plain,(
% 41.89/5.67    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl29_6),
% 41.89/5.67    inference(resolution,[],[f343,f470])).
% 41.89/5.67  fof(f597,plain,(
% 41.89/5.67    spl29_21),
% 41.89/5.67    inference(avatar_split_clause,[],[f591,f593])).
% 41.89/5.67  fof(f591,plain,(
% 41.89/5.67    m1_subset_1(sK13(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 41.89/5.67    inference(superposition,[],[f291,f429])).
% 41.89/5.67  fof(f291,plain,(
% 41.89/5.67    ( ! [X0] : (m1_subset_1(sK13(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 41.89/5.67    inference(cnf_transformation,[],[f178])).
% 41.89/5.67  fof(f178,plain,(
% 41.89/5.67    ! [X0] : (v3_funct_2(sK13(X0),X0,X0) & v1_funct_2(sK13(X0),X0,X0) & v1_funct_1(sK13(X0)) & v5_relat_1(sK13(X0),X0) & v4_relat_1(sK13(X0),X0) & v1_relat_1(sK13(X0)) & m1_subset_1(sK13(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 41.89/5.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f68,f177])).
% 41.89/5.67  fof(f177,plain,(
% 41.89/5.67    ! [X0] : (? [X1] : (v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v4_relat_1(X1,X0) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (v3_funct_2(sK13(X0),X0,X0) & v1_funct_2(sK13(X0),X0,X0) & v1_funct_1(sK13(X0)) & v5_relat_1(sK13(X0),X0) & v4_relat_1(sK13(X0),X0) & v1_relat_1(sK13(X0)) & m1_subset_1(sK13(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))))),
% 41.89/5.67    introduced(choice_axiom,[])).
% 41.89/5.67  fof(f68,axiom,(
% 41.89/5.67    ! [X0] : ? [X1] : (v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v4_relat_1(X1,X0) & v1_relat_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_2)).
% 41.89/5.67  fof(f532,plain,(
% 41.89/5.67    spl29_18),
% 41.89/5.67    inference(avatar_split_clause,[],[f244,f529])).
% 41.89/5.67  fof(f244,plain,(
% 41.89/5.67    v1_relat_1(k1_xboole_0)),
% 41.89/5.67    inference(cnf_transformation,[],[f50])).
% 41.89/5.67  fof(f50,axiom,(
% 41.89/5.67    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 41.89/5.67  fof(f527,plain,(
% 41.89/5.67    spl29_17),
% 41.89/5.67    inference(avatar_split_clause,[],[f246,f524])).
% 41.89/5.67  fof(f246,plain,(
% 41.89/5.67    v1_funct_1(k1_xboole_0)),
% 41.89/5.67    inference(cnf_transformation,[],[f50])).
% 41.89/5.67  fof(f517,plain,(
% 41.89/5.67    spl29_15),
% 41.89/5.67    inference(avatar_split_clause,[],[f233,f514])).
% 41.89/5.67  fof(f233,plain,(
% 41.89/5.67    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 41.89/5.67    inference(cnf_transformation,[],[f42])).
% 41.89/5.67  fof(f42,axiom,(
% 41.89/5.67    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 41.89/5.67  fof(f512,plain,(
% 41.89/5.67    spl29_14),
% 41.89/5.67    inference(avatar_split_clause,[],[f234,f509])).
% 41.89/5.67  fof(f234,plain,(
% 41.89/5.67    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 41.89/5.67    inference(cnf_transformation,[],[f42])).
% 41.89/5.67  fof(f502,plain,(
% 41.89/5.67    spl29_12),
% 41.89/5.67    inference(avatar_split_clause,[],[f393,f499])).
% 41.89/5.67  fof(f393,plain,(
% 41.89/5.67    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 41.89/5.67    inference(definition_unfolding,[],[f231,f239])).
% 41.89/5.67  fof(f231,plain,(
% 41.89/5.67    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 41.89/5.67    inference(cnf_transformation,[],[f46])).
% 41.89/5.67  fof(f46,axiom,(
% 41.89/5.67    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 41.89/5.67  fof(f497,plain,(
% 41.89/5.67    spl29_11),
% 41.89/5.67    inference(avatar_split_clause,[],[f218,f494])).
% 41.89/5.67  fof(f218,plain,(
% 41.89/5.67    v2_pre_topc(sK0)),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f154,plain,(
% 41.89/5.67    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 41.89/5.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f149,f153,f152,f151,f150])).
% 41.89/5.67  fof(f150,plain,(
% 41.89/5.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 41.89/5.67    introduced(choice_axiom,[])).
% 41.89/5.67  fof(f151,plain,(
% 41.89/5.67    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 41.89/5.67    introduced(choice_axiom,[])).
% 41.89/5.67  fof(f152,plain,(
% 41.89/5.67    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 41.89/5.67    introduced(choice_axiom,[])).
% 41.89/5.67  fof(f153,plain,(
% 41.89/5.67    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 41.89/5.67    introduced(choice_axiom,[])).
% 41.89/5.67  fof(f149,plain,(
% 41.89/5.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 41.89/5.67    inference(flattening,[],[f148])).
% 41.89/5.67  fof(f148,plain,(
% 41.89/5.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 41.89/5.67    inference(nnf_transformation,[],[f83])).
% 41.89/5.67  fof(f83,plain,(
% 41.89/5.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 41.89/5.67    inference(flattening,[],[f82])).
% 41.89/5.67  fof(f82,plain,(
% 41.89/5.67    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 41.89/5.67    inference(ennf_transformation,[],[f81])).
% 41.89/5.67  fof(f81,negated_conjecture,(
% 41.89/5.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 41.89/5.67    inference(negated_conjecture,[],[f80])).
% 41.89/5.67  fof(f80,conjecture,(
% 41.89/5.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 41.89/5.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 41.89/5.67  fof(f492,plain,(
% 41.89/5.67    spl29_10),
% 41.89/5.67    inference(avatar_split_clause,[],[f219,f489])).
% 41.89/5.67  fof(f219,plain,(
% 41.89/5.67    l1_pre_topc(sK0)),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f487,plain,(
% 41.89/5.67    spl29_9),
% 41.89/5.67    inference(avatar_split_clause,[],[f220,f484])).
% 41.89/5.67  fof(f220,plain,(
% 41.89/5.67    v2_pre_topc(sK1)),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f482,plain,(
% 41.89/5.67    spl29_8),
% 41.89/5.67    inference(avatar_split_clause,[],[f221,f479])).
% 41.89/5.67  fof(f221,plain,(
% 41.89/5.67    l1_pre_topc(sK1)),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f477,plain,(
% 41.89/5.67    spl29_5),
% 41.89/5.67    inference(avatar_split_clause,[],[f392,f463])).
% 41.89/5.67  fof(f392,plain,(
% 41.89/5.67    v1_funct_1(sK3)),
% 41.89/5.67    inference(definition_unfolding,[],[f222,f228])).
% 41.89/5.67  fof(f228,plain,(
% 41.89/5.67    sK2 = sK3),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f222,plain,(
% 41.89/5.67    v1_funct_1(sK2)),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f476,plain,(
% 41.89/5.67    spl29_7),
% 41.89/5.67    inference(avatar_split_clause,[],[f391,f473])).
% 41.89/5.67  fof(f391,plain,(
% 41.89/5.67    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 41.89/5.67    inference(definition_unfolding,[],[f223,f228])).
% 41.89/5.67  fof(f223,plain,(
% 41.89/5.67    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f471,plain,(
% 41.89/5.67    spl29_6),
% 41.89/5.67    inference(avatar_split_clause,[],[f390,f468])).
% 41.89/5.67  fof(f390,plain,(
% 41.89/5.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 41.89/5.67    inference(definition_unfolding,[],[f224,f228])).
% 41.89/5.67  fof(f224,plain,(
% 41.89/5.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f461,plain,(
% 41.89/5.67    spl29_4),
% 41.89/5.67    inference(avatar_split_clause,[],[f226,f458])).
% 41.89/5.67  fof(f226,plain,(
% 41.89/5.67    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f456,plain,(
% 41.89/5.67    spl29_3),
% 41.89/5.67    inference(avatar_split_clause,[],[f227,f453])).
% 41.89/5.67  fof(f227,plain,(
% 41.89/5.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f451,plain,(
% 41.89/5.67    spl29_1 | spl29_2),
% 41.89/5.67    inference(avatar_split_clause,[],[f389,f447,f443])).
% 41.89/5.67  fof(f389,plain,(
% 41.89/5.67    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK3,sK0,sK1)),
% 41.89/5.67    inference(definition_unfolding,[],[f229,f228])).
% 41.89/5.67  fof(f229,plain,(
% 41.89/5.67    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  fof(f450,plain,(
% 41.89/5.67    ~spl29_1 | ~spl29_2),
% 41.89/5.67    inference(avatar_split_clause,[],[f388,f447,f443])).
% 41.89/5.67  fof(f388,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK3,sK0,sK1)),
% 41.89/5.67    inference(definition_unfolding,[],[f230,f228])).
% 41.89/5.67  fof(f230,plain,(
% 41.89/5.67    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 41.89/5.67    inference(cnf_transformation,[],[f154])).
% 41.89/5.67  % SZS output end Proof for theBenchmark
% 41.89/5.67  % (7794)------------------------------
% 41.89/5.67  % (7794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.89/5.67  % (7794)Termination reason: Refutation
% 41.89/5.67  
% 41.89/5.67  % (7794)Memory used [KB]: 61662
% 41.89/5.67  % (7794)Time elapsed: 5.073 s
% 41.89/5.67  % (7794)------------------------------
% 41.89/5.67  % (7794)------------------------------
% 41.89/5.68  % (7751)Success in time 5.319 s
%------------------------------------------------------------------------------
