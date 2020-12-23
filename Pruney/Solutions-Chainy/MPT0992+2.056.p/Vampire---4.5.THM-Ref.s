%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:18 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  316 ( 600 expanded)
%              Number of leaves         :   70 ( 247 expanded)
%              Depth                    :   11
%              Number of atoms          :  918 (1868 expanded)
%              Number of equality atoms :  168 ( 419 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f136,f142,f148,f157,f166,f174,f182,f193,f202,f206,f244,f287,f304,f317,f371,f391,f435,f477,f716,f752,f805,f826,f844,f890,f921,f981,f1003,f1087,f1093,f1143,f1196,f1506,f1574,f1857,f1903,f1924,f2248,f2258,f2264,f2350,f2527,f2574,f2614,f2618,f2637,f2644,f2708,f2720])).

fof(f2720,plain,
    ( spl4_6
    | ~ spl4_146
    | spl4_154
    | ~ spl4_157 ),
    inference(avatar_contradiction_clause,[],[f2719])).

fof(f2719,plain,
    ( $false
    | spl4_6
    | ~ spl4_146
    | spl4_154
    | ~ spl4_157 ),
    inference(subsumption_resolution,[],[f2718,f2525])).

fof(f2525,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_146 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f2524,plain,
    ( spl4_146
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f2718,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_6
    | spl4_154
    | ~ spl4_157 ),
    inference(subsumption_resolution,[],[f2717,f152])).

fof(f152,plain,
    ( k1_xboole_0 != sK1
    | spl4_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2717,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_154
    | ~ spl4_157 ),
    inference(subsumption_resolution,[],[f2715,f2643])).

fof(f2643,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_154 ),
    inference(avatar_component_clause,[],[f2641])).

fof(f2641,plain,
    ( spl4_154
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f2715,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_157 ),
    inference(trivial_inequality_removal,[],[f2714])).

fof(f2714,plain,
    ( sK2 != sK2
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_157 ),
    inference(superposition,[],[f107,f2707])).

fof(f2707,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_157 ),
    inference(avatar_component_clause,[],[f2705])).

fof(f2705,plain,
    ( spl4_157
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_157])])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f2708,plain,
    ( spl4_157
    | ~ spl4_146
    | ~ spl4_152 ),
    inference(avatar_split_clause,[],[f2678,f2611,f2524,f2705])).

fof(f2611,plain,
    ( spl4_152
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f2678,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_146
    | ~ spl4_152 ),
    inference(forward_demodulation,[],[f2672,f2613])).

fof(f2613,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_152 ),
    inference(avatar_component_clause,[],[f2611])).

fof(f2672,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_146 ),
    inference(resolution,[],[f2525,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f2644,plain,
    ( ~ spl4_154
    | spl4_30
    | ~ spl4_113 ),
    inference(avatar_split_clause,[],[f2639,f1973,f428,f2641])).

fof(f428,plain,
    ( spl4_30
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1973,plain,
    ( spl4_113
  <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).

fof(f2639,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_30
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f430,f1974])).

fof(f1974,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_113 ),
    inference(avatar_component_clause,[],[f1973])).

fof(f430,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f428])).

fof(f2637,plain,
    ( ~ spl4_52
    | spl4_146
    | ~ spl4_153 ),
    inference(avatar_contradiction_clause,[],[f2636])).

fof(f2636,plain,
    ( $false
    | ~ spl4_52
    | spl4_146
    | ~ spl4_153 ),
    inference(subsumption_resolution,[],[f2632,f2526])).

fof(f2526,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_146 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f2632,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_52
    | ~ spl4_153 ),
    inference(resolution,[],[f2617,f843])).

fof(f843,plain,
    ( ! [X3] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f842])).

fof(f842,plain,
    ( spl4_52
  <=> ! [X3] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f2617,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) )
    | ~ spl4_153 ),
    inference(avatar_component_clause,[],[f2616])).

fof(f2616,plain,
    ( spl4_153
  <=> ! [X9] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).

fof(f2618,plain,
    ( spl4_153
    | ~ spl4_2
    | ~ spl4_138
    | ~ spl4_151 ),
    inference(avatar_split_clause,[],[f2609,f2572,f2348,f128,f2616])).

fof(f128,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2348,plain,
    ( spl4_138
  <=> ! [X9] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f2572,plain,
    ( spl4_151
  <=> ! [X7] :
        ( ~ r1_tarski(X7,sK0)
        | k1_relat_1(k7_relat_1(sK3,X7)) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).

fof(f2609,plain,
    ( ! [X9] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9) )
    | ~ spl4_2
    | ~ spl4_138
    | ~ spl4_151 ),
    inference(backward_demodulation,[],[f2349,f2606])).

fof(f2606,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_151 ),
    inference(resolution,[],[f2573,f130])).

fof(f130,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f2573,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,sK0)
        | k1_relat_1(k7_relat_1(sK3,X7)) = X7 )
    | ~ spl4_151 ),
    inference(avatar_component_clause,[],[f2572])).

fof(f2349,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9))) )
    | ~ spl4_138 ),
    inference(avatar_component_clause,[],[f2348])).

fof(f2614,plain,
    ( spl4_152
    | ~ spl4_2
    | ~ spl4_151 ),
    inference(avatar_split_clause,[],[f2606,f2572,f128,f2611])).

fof(f2574,plain,
    ( spl4_151
    | ~ spl4_10
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f2561,f388,f179,f2572])).

fof(f179,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f388,plain,
    ( spl4_28
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f2561,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,sK0)
        | k1_relat_1(k7_relat_1(sK3,X7)) = X7 )
    | ~ spl4_10
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f279,f390])).

fof(f390,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f388])).

fof(f279,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,k1_relat_1(sK3))
        | k1_relat_1(k7_relat_1(sK3,X7)) = X7 )
    | ~ spl4_10 ),
    inference(resolution,[],[f82,f181])).

fof(f181,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f2527,plain,
    ( ~ spl4_146
    | spl4_31
    | ~ spl4_113 ),
    inference(avatar_split_clause,[],[f2505,f1973,f432,f2524])).

fof(f432,plain,
    ( spl4_31
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f2505,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_31
    | ~ spl4_113 ),
    inference(backward_demodulation,[],[f434,f1974])).

fof(f434,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f432])).

fof(f2350,plain,
    ( spl4_138
    | ~ spl4_108
    | ~ spl4_136 ),
    inference(avatar_split_clause,[],[f2271,f2255,f1922,f2348])).

fof(f1922,plain,
    ( spl4_108
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f2255,plain,
    ( spl4_136
  <=> v1_funct_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f2271,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9))) )
    | ~ spl4_108
    | ~ spl4_136 ),
    inference(subsumption_resolution,[],[f2268,f1923])).

fof(f1923,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f1922])).

fof(f2268,plain,
    ( ! [X9] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9)))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_136 ),
    inference(resolution,[],[f2256,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f2256,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ spl4_136 ),
    inference(avatar_component_clause,[],[f2255])).

fof(f2264,plain,
    ( ~ spl4_1
    | ~ spl4_10
    | spl4_136 ),
    inference(avatar_contradiction_clause,[],[f2263])).

fof(f2263,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_10
    | spl4_136 ),
    inference(subsumption_resolution,[],[f2262,f181])).

fof(f2262,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_1
    | spl4_136 ),
    inference(subsumption_resolution,[],[f2260,f125])).

fof(f125,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2260,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_136 ),
    inference(resolution,[],[f2257,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f2257,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | spl4_136 ),
    inference(avatar_component_clause,[],[f2255])).

fof(f2258,plain,
    ( ~ spl4_136
    | ~ spl4_5
    | spl4_29
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f2244,f714,f424,f145,f2255])).

fof(f145,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f424,plain,
    ( spl4_29
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f714,plain,
    ( spl4_44
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f2244,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ spl4_5
    | spl4_29
    | ~ spl4_44 ),
    inference(backward_demodulation,[],[f426,f1716])).

fof(f1716,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_5
    | ~ spl4_44 ),
    inference(resolution,[],[f715,f147])).

fof(f147,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f715,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2) )
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f714])).

fof(f426,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f424])).

fof(f2248,plain,
    ( spl4_113
    | ~ spl4_5
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f1716,f714,f145,f1973])).

fof(f1924,plain,
    ( spl4_108
    | ~ spl4_33
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1908,f1901,f475,f1922])).

fof(f475,plain,
    ( spl4_33
  <=> ! [X7] :
        ( v1_relat_1(X7)
        | ~ r1_tarski(X7,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1901,plain,
    ( spl4_106
  <=> ! [X2] : r1_tarski(k7_relat_1(sK3,X2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f1908,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl4_33
    | ~ spl4_106 ),
    inference(resolution,[],[f1902,f476])).

fof(f476,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,sK3)
        | v1_relat_1(X7) )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f475])).

fof(f1902,plain,
    ( ! [X2] : r1_tarski(k7_relat_1(sK3,X2),sK3)
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f1901])).

fof(f1903,plain,
    ( spl4_106
    | ~ spl4_103 ),
    inference(avatar_split_clause,[],[f1899,f1844,f1901])).

fof(f1844,plain,
    ( spl4_103
  <=> ! [X11,X10] :
        ( r1_tarski(k7_relat_1(sK3,X10),X11)
        | ~ r1_tarski(sK3,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).

fof(f1899,plain,
    ( ! [X2] : r1_tarski(k7_relat_1(sK3,X2),sK3)
    | ~ spl4_103 ),
    inference(resolution,[],[f1845,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1845,plain,
    ( ! [X10,X11] :
        ( ~ r1_tarski(sK3,X11)
        | r1_tarski(k7_relat_1(sK3,X10),X11) )
    | ~ spl4_103 ),
    inference(avatar_component_clause,[],[f1844])).

fof(f1857,plain,
    ( spl4_103
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f1540,f179,f1844])).

fof(f1540,plain,
    ( ! [X15,X16] :
        ( r1_tarski(k7_relat_1(sK3,X15),X16)
        | ~ r1_tarski(sK3,X16) )
    | ~ spl4_10 ),
    inference(resolution,[],[f181,f256])).

fof(f256,plain,(
    ! [X14,X15,X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(k7_relat_1(X13,X15),X14)
      | ~ r1_tarski(X13,X14) ) ),
    inference(resolution,[],[f111,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1574,plain,
    ( spl4_16
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f1566,f145,f260])).

fof(f260,plain,
    ( spl4_16
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1566,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f147,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1506,plain,
    ( ~ spl4_7
    | spl4_30
    | ~ spl4_49
    | ~ spl4_64
    | ~ spl4_70
    | ~ spl4_77 ),
    inference(avatar_contradiction_clause,[],[f1505])).

fof(f1505,plain,
    ( $false
    | ~ spl4_7
    | spl4_30
    | ~ spl4_49
    | ~ spl4_64
    | ~ spl4_70
    | ~ spl4_77 ),
    inference(subsumption_resolution,[],[f1504,f825])).

fof(f825,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f824])).

fof(f824,plain,
    ( spl4_49
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f1504,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_7
    | spl4_30
    | ~ spl4_64
    | ~ spl4_70
    | ~ spl4_77 ),
    inference(forward_demodulation,[],[f1503,f1195])).

fof(f1195,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2)
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f1194])).

fof(f1194,plain,
    ( spl4_77
  <=> ! [X1,X0,X2] : k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f1503,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_7
    | spl4_30
    | ~ spl4_64
    | ~ spl4_70 ),
    inference(forward_demodulation,[],[f1450,f1086])).

fof(f1086,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f1084])).

fof(f1084,plain,
    ( spl4_70
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f1450,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_7
    | spl4_30
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f1449,f156])).

fof(f156,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1449,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_30
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f430,f1002])).

fof(f1002,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1000,plain,
    ( spl4_64
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f1196,plain,
    ( spl4_77
    | ~ spl4_13
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f1149,f1141,f204,f1194])).

fof(f204,plain,
    ( spl4_13
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1141,plain,
    ( spl4_75
  <=> ! [X7,X8,X6] :
        ( k1_xboole_0 = k2_partfun1(X6,X7,k1_xboole_0,X8)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f1149,plain,
    ( ! [X2,X0,X1] : k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2)
    | ~ spl4_13
    | ~ spl4_75 ),
    inference(subsumption_resolution,[],[f1146,f205])).

fof(f205,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f204])).

fof(f1146,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2)
        | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) )
    | ~ spl4_75 ),
    inference(resolution,[],[f1142,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1142,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k1_xboole_0 = k2_partfun1(X6,X7,k1_xboole_0,X8) )
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f1141])).

fof(f1143,plain,
    ( spl4_75
    | ~ spl4_9
    | ~ spl4_71 ),
    inference(avatar_split_clause,[],[f1106,f1090,f172,f1141])).

fof(f172,plain,
    ( spl4_9
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1090,plain,
    ( spl4_71
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1106,plain,
    ( ! [X6,X8,X7] :
        ( k1_xboole_0 = k2_partfun1(X6,X7,k1_xboole_0,X8)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl4_9
    | ~ spl4_71 ),
    inference(forward_demodulation,[],[f1096,f173])).

fof(f173,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1096,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k2_partfun1(X6,X7,k1_xboole_0,X8) = k7_relat_1(k1_xboole_0,X8) )
    | ~ spl4_71 ),
    inference(resolution,[],[f1092,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f1092,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1093,plain,
    ( spl4_71
    | ~ spl4_1
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f1073,f978,f123,f1090])).

fof(f978,plain,
    ( spl4_60
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f1073,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_60 ),
    inference(backward_demodulation,[],[f125,f1016])).

fof(f1016,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_60 ),
    inference(resolution,[],[f980,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f980,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f978])).

fof(f1087,plain,
    ( spl4_70
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f1016,f978,f1084])).

fof(f1003,plain,
    ( spl4_64
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f923,f918,f1000])).

fof(f918,plain,
    ( spl4_55
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f923,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_55 ),
    inference(resolution,[],[f920,f75])).

fof(f920,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f918])).

fof(f981,plain,
    ( spl4_60
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f903,f163,f150,f978])).

fof(f163,plain,
    ( spl4_8
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f903,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f897,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f897,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f165,f151])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f165,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f921,plain,
    ( spl4_55
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f904,f154,f128,f918])).

fof(f904,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f130,f156])).

fof(f890,plain,
    ( sK3 != k7_relat_1(sK3,sK0)
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f844,plain,
    ( spl4_52
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f652,f284,f179,f842])).

fof(f284,plain,
    ( spl4_18
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f652,plain,
    ( ! [X3] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1)
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f649,f181])).

fof(f649,plain,
    ( ! [X3] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_18 ),
    inference(resolution,[],[f255,f286])).

fof(f286,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f284])).

fof(f255,plain,(
    ! [X12,X10,X11] :
      ( ~ r1_tarski(k2_relat_1(X10),X11)
      | r1_tarski(k2_relat_1(k7_relat_1(X10,X12)),X11)
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f111,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f826,plain,
    ( spl4_49
    | ~ spl4_21
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f814,f803,f309,f824])).

fof(f309,plain,
    ( spl4_21
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f803,plain,
    ( spl4_47
  <=> ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f814,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_21
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f813,f310])).

fof(f310,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f309])).

fof(f813,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_47 ),
    inference(trivial_inequality_removal,[],[f810])).

fof(f810,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_47 ),
    inference(superposition,[],[f353,f804])).

fof(f804,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f803])).

fof(f353,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f120,f116])).

fof(f116,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f120,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f805,plain,
    ( spl4_47
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f607,f309,f199,f803])).

fof(f199,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f607,plain,
    ( ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f605,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f605,plain,
    ( ! [X0] : k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl4_21 ),
    inference(resolution,[],[f295,f310])).

fof(f295,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3) ) ),
    inference(superposition,[],[f102,f116])).

fof(f752,plain,
    ( spl4_45
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f502,f179,f749])).

fof(f749,plain,
    ( spl4_45
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f502,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_10 ),
    inference(resolution,[],[f183,f181])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f79,f75])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f716,plain,
    ( spl4_44
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f372,f123,f714])).

fof(f372,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f112,f125])).

fof(f477,plain,
    ( spl4_33
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f473,f179,f475])).

fof(f473,plain,
    ( ! [X7] :
        ( v1_relat_1(X7)
        | ~ r1_tarski(X7,sK3) )
    | ~ spl4_10 ),
    inference(resolution,[],[f176,f181])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f74,f97])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f435,plain,
    ( ~ spl4_29
    | ~ spl4_30
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f72,f432,f428,f424])).

fof(f72,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f57])).

fof(f57,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f391,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f379,f368,f150,f145,f133,f388])).

fof(f133,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f368,plain,
    ( spl4_26
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f379,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f370,f378])).

fof(f378,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f377,f147])).

fof(f377,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | spl4_6 ),
    inference(subsumption_resolution,[],[f374,f152])).

fof(f374,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f105,f135])).

fof(f135,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f370,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f368])).

fof(f371,plain,
    ( spl4_26
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f292,f145,f368])).

fof(f292,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_5 ),
    inference(resolution,[],[f102,f147])).

fof(f317,plain,
    ( ~ spl4_13
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl4_13
    | spl4_21 ),
    inference(subsumption_resolution,[],[f314,f205])).

fof(f314,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_21 ),
    inference(resolution,[],[f311,f97])).

fof(f311,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f309])).

fof(f304,plain,
    ( spl4_19
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f266,f241,f179,f301])).

fof(f301,plain,
    ( spl4_19
  <=> sK3 = k7_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f241,plain,
    ( spl4_15
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f266,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f265,f181])).

fof(f265,plain,
    ( sK3 = k7_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(resolution,[],[f92,f243])).

fof(f243,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f241])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f287,plain,
    ( spl4_18
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f268,f260,f179,f284])).

fof(f268,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f267,f181])).

fof(f267,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_16 ),
    inference(resolution,[],[f262,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f262,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f260])).

fof(f244,plain,
    ( spl4_15
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f236,f145,f241])).

fof(f236,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f103,f147])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f206,plain,
    ( spl4_13
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f197,f191,f204])).

fof(f191,plain,
    ( spl4_11
  <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f197,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f192,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(resolution,[],[f192,f75])).

fof(f192,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f202,plain,
    ( spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f195,f191,f199])).

fof(f193,plain,
    ( spl4_11
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f188,f172,f139,f191])).

fof(f139,plain,
    ( spl4_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f188,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f185,f141])).

fof(f141,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f185,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_9 ),
    inference(superposition,[],[f79,f173])).

fof(f182,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f177,f145,f179])).

fof(f177,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f175,f76])).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f175,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f74,f147])).

fof(f174,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f160,f139,f172])).

fof(f160,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f159,f141])).

fof(f159,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f78,f75])).

fof(f166,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f161,f145,f163])).

fof(f161,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f96,f147])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f157,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f71,f154,f150])).

fof(f71,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f58])).

fof(f148,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f69,f145])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f142,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f137,f139])).

fof(f137,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f76,f115])).

fof(f136,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f68,f133])).

fof(f68,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f131,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f70,f128])).

fof(f70,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f126,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f67,f123])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.06/0.25  % Computer   : n013.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 20:37:09 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.10/0.40  % (25288)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.10/0.40  % (25290)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.10/0.40  % (25287)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.10/0.40  % (25294)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.10/0.40  % (25289)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.10/0.41  % (25305)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.10/0.41  % (25303)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.10/0.41  % (25306)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.10/0.41  % (25310)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.10/0.42  % (25295)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.10/0.42  % (25307)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.10/0.42  % (25302)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.10/0.42  % (25304)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.10/0.42  % (25297)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.10/0.42  % (25299)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.10/0.43  % (25296)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.10/0.43  % (25298)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.10/0.43  % (25285)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.10/0.43  % (25293)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.10/0.43  % (25291)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.10/0.43  % (25309)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.10/0.44  % (25292)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.10/0.44  % (25301)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.10/0.44  % (25286)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.10/0.44  % (25308)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.10/0.45  % (25300)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 2.06/0.56  % (25287)Refutation found. Thanks to Tanya!
% 2.06/0.56  % SZS status Theorem for theBenchmark
% 2.06/0.56  % SZS output start Proof for theBenchmark
% 2.06/0.56  fof(f2721,plain,(
% 2.06/0.56    $false),
% 2.06/0.56    inference(avatar_sat_refutation,[],[f126,f131,f136,f142,f148,f157,f166,f174,f182,f193,f202,f206,f244,f287,f304,f317,f371,f391,f435,f477,f716,f752,f805,f826,f844,f890,f921,f981,f1003,f1087,f1093,f1143,f1196,f1506,f1574,f1857,f1903,f1924,f2248,f2258,f2264,f2350,f2527,f2574,f2614,f2618,f2637,f2644,f2708,f2720])).
% 2.06/0.56  fof(f2720,plain,(
% 2.06/0.56    spl4_6 | ~spl4_146 | spl4_154 | ~spl4_157),
% 2.06/0.56    inference(avatar_contradiction_clause,[],[f2719])).
% 2.06/0.56  fof(f2719,plain,(
% 2.06/0.56    $false | (spl4_6 | ~spl4_146 | spl4_154 | ~spl4_157)),
% 2.06/0.56    inference(subsumption_resolution,[],[f2718,f2525])).
% 2.06/0.56  fof(f2525,plain,(
% 2.06/0.56    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_146),
% 2.06/0.56    inference(avatar_component_clause,[],[f2524])).
% 2.06/0.56  fof(f2524,plain,(
% 2.06/0.56    spl4_146 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).
% 2.06/0.56  fof(f2718,plain,(
% 2.06/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_6 | spl4_154 | ~spl4_157)),
% 2.06/0.56    inference(subsumption_resolution,[],[f2717,f152])).
% 2.06/0.56  fof(f152,plain,(
% 2.06/0.56    k1_xboole_0 != sK1 | spl4_6),
% 2.06/0.56    inference(avatar_component_clause,[],[f150])).
% 2.06/0.56  fof(f150,plain,(
% 2.06/0.56    spl4_6 <=> k1_xboole_0 = sK1),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.06/0.56  fof(f2717,plain,(
% 2.06/0.56    k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_154 | ~spl4_157)),
% 2.06/0.56    inference(subsumption_resolution,[],[f2715,f2643])).
% 2.06/0.56  fof(f2643,plain,(
% 2.06/0.56    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_154),
% 2.06/0.56    inference(avatar_component_clause,[],[f2641])).
% 2.06/0.56  fof(f2641,plain,(
% 2.06/0.56    spl4_154 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).
% 2.06/0.56  fof(f2715,plain,(
% 2.06/0.56    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_157),
% 2.06/0.56    inference(trivial_inequality_removal,[],[f2714])).
% 2.06/0.56  fof(f2714,plain,(
% 2.06/0.56    sK2 != sK2 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_157),
% 2.06/0.56    inference(superposition,[],[f107,f2707])).
% 2.06/0.56  fof(f2707,plain,(
% 2.06/0.56    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_157),
% 2.06/0.56    inference(avatar_component_clause,[],[f2705])).
% 2.06/0.56  fof(f2705,plain,(
% 2.06/0.56    spl4_157 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_157])])).
% 2.06/0.56  fof(f107,plain,(
% 2.06/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.56    inference(cnf_transformation,[],[f66])).
% 2.06/0.56  fof(f66,plain,(
% 2.06/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.56    inference(nnf_transformation,[],[f52])).
% 2.06/0.56  fof(f52,plain,(
% 2.06/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.56    inference(flattening,[],[f51])).
% 2.06/0.56  fof(f51,plain,(
% 2.06/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.56    inference(ennf_transformation,[],[f22])).
% 2.06/0.56  fof(f22,axiom,(
% 2.06/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.06/0.56  fof(f2708,plain,(
% 2.06/0.56    spl4_157 | ~spl4_146 | ~spl4_152),
% 2.06/0.56    inference(avatar_split_clause,[],[f2678,f2611,f2524,f2705])).
% 2.06/0.56  fof(f2611,plain,(
% 2.06/0.56    spl4_152 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).
% 2.06/0.56  fof(f2678,plain,(
% 2.06/0.56    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_146 | ~spl4_152)),
% 2.06/0.56    inference(forward_demodulation,[],[f2672,f2613])).
% 2.06/0.56  fof(f2613,plain,(
% 2.06/0.56    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_152),
% 2.06/0.56    inference(avatar_component_clause,[],[f2611])).
% 2.06/0.56  fof(f2672,plain,(
% 2.06/0.56    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_146),
% 2.06/0.56    inference(resolution,[],[f2525,f102])).
% 2.06/0.56  fof(f102,plain,(
% 2.06/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.06/0.56    inference(cnf_transformation,[],[f49])).
% 2.06/0.56  fof(f49,plain,(
% 2.06/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.56    inference(ennf_transformation,[],[f21])).
% 2.06/0.56  fof(f21,axiom,(
% 2.06/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.06/0.56  fof(f2644,plain,(
% 2.06/0.56    ~spl4_154 | spl4_30 | ~spl4_113),
% 2.06/0.56    inference(avatar_split_clause,[],[f2639,f1973,f428,f2641])).
% 2.06/0.56  fof(f428,plain,(
% 2.06/0.56    spl4_30 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 2.06/0.56  fof(f1973,plain,(
% 2.06/0.56    spl4_113 <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).
% 2.06/0.56  fof(f2639,plain,(
% 2.06/0.56    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_30 | ~spl4_113)),
% 2.06/0.56    inference(forward_demodulation,[],[f430,f1974])).
% 2.06/0.56  fof(f1974,plain,(
% 2.06/0.56    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | ~spl4_113),
% 2.06/0.56    inference(avatar_component_clause,[],[f1973])).
% 2.06/0.56  fof(f430,plain,(
% 2.06/0.56    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_30),
% 2.06/0.56    inference(avatar_component_clause,[],[f428])).
% 2.06/0.56  fof(f2637,plain,(
% 2.06/0.56    ~spl4_52 | spl4_146 | ~spl4_153),
% 2.06/0.56    inference(avatar_contradiction_clause,[],[f2636])).
% 2.06/0.56  fof(f2636,plain,(
% 2.06/0.56    $false | (~spl4_52 | spl4_146 | ~spl4_153)),
% 2.06/0.56    inference(subsumption_resolution,[],[f2632,f2526])).
% 2.06/0.56  fof(f2526,plain,(
% 2.06/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_146),
% 2.06/0.56    inference(avatar_component_clause,[],[f2524])).
% 2.06/0.56  fof(f2632,plain,(
% 2.06/0.56    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_52 | ~spl4_153)),
% 2.06/0.56    inference(resolution,[],[f2617,f843])).
% 2.06/0.56  fof(f843,plain,(
% 2.06/0.56    ( ! [X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1)) ) | ~spl4_52),
% 2.06/0.56    inference(avatar_component_clause,[],[f842])).
% 2.06/0.56  fof(f842,plain,(
% 2.06/0.56    spl4_52 <=> ! [X3] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.06/0.56  fof(f2617,plain,(
% 2.06/0.56    ( ! [X9] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9)))) ) | ~spl4_153),
% 2.06/0.56    inference(avatar_component_clause,[],[f2616])).
% 2.06/0.56  fof(f2616,plain,(
% 2.06/0.56    spl4_153 <=> ! [X9] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).
% 2.06/0.56  fof(f2618,plain,(
% 2.06/0.56    spl4_153 | ~spl4_2 | ~spl4_138 | ~spl4_151),
% 2.06/0.56    inference(avatar_split_clause,[],[f2609,f2572,f2348,f128,f2616])).
% 2.06/0.56  fof(f128,plain,(
% 2.06/0.56    spl4_2 <=> r1_tarski(sK2,sK0)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.06/0.56  fof(f2348,plain,(
% 2.06/0.56    spl4_138 <=> ! [X9] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9))))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).
% 2.06/0.56  fof(f2572,plain,(
% 2.06/0.56    spl4_151 <=> ! [X7] : (~r1_tarski(X7,sK0) | k1_relat_1(k7_relat_1(sK3,X7)) = X7)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).
% 2.06/0.56  fof(f2609,plain,(
% 2.06/0.56    ( ! [X9] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9)) ) | (~spl4_2 | ~spl4_138 | ~spl4_151)),
% 2.06/0.56    inference(backward_demodulation,[],[f2349,f2606])).
% 2.06/0.56  fof(f2606,plain,(
% 2.06/0.56    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_151)),
% 2.06/0.56    inference(resolution,[],[f2573,f130])).
% 2.06/0.56  fof(f130,plain,(
% 2.06/0.56    r1_tarski(sK2,sK0) | ~spl4_2),
% 2.06/0.56    inference(avatar_component_clause,[],[f128])).
% 2.06/0.56  fof(f2573,plain,(
% 2.06/0.56    ( ! [X7] : (~r1_tarski(X7,sK0) | k1_relat_1(k7_relat_1(sK3,X7)) = X7) ) | ~spl4_151),
% 2.06/0.56    inference(avatar_component_clause,[],[f2572])).
% 2.06/0.56  fof(f2349,plain,(
% 2.06/0.56    ( ! [X9] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9)))) ) | ~spl4_138),
% 2.06/0.56    inference(avatar_component_clause,[],[f2348])).
% 2.06/0.56  fof(f2614,plain,(
% 2.06/0.56    spl4_152 | ~spl4_2 | ~spl4_151),
% 2.06/0.56    inference(avatar_split_clause,[],[f2606,f2572,f128,f2611])).
% 2.06/0.56  fof(f2574,plain,(
% 2.06/0.56    spl4_151 | ~spl4_10 | ~spl4_28),
% 2.06/0.56    inference(avatar_split_clause,[],[f2561,f388,f179,f2572])).
% 2.06/0.56  fof(f179,plain,(
% 2.06/0.56    spl4_10 <=> v1_relat_1(sK3)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.06/0.56  fof(f388,plain,(
% 2.06/0.56    spl4_28 <=> sK0 = k1_relat_1(sK3)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.06/0.56  fof(f2561,plain,(
% 2.06/0.56    ( ! [X7] : (~r1_tarski(X7,sK0) | k1_relat_1(k7_relat_1(sK3,X7)) = X7) ) | (~spl4_10 | ~spl4_28)),
% 2.06/0.56    inference(forward_demodulation,[],[f279,f390])).
% 2.06/0.56  fof(f390,plain,(
% 2.06/0.56    sK0 = k1_relat_1(sK3) | ~spl4_28),
% 2.06/0.56    inference(avatar_component_clause,[],[f388])).
% 2.06/0.56  fof(f279,plain,(
% 2.06/0.56    ( ! [X7] : (~r1_tarski(X7,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X7)) = X7) ) | ~spl4_10),
% 2.06/0.56    inference(resolution,[],[f82,f181])).
% 2.06/0.56  fof(f181,plain,(
% 2.06/0.56    v1_relat_1(sK3) | ~spl4_10),
% 2.06/0.56    inference(avatar_component_clause,[],[f179])).
% 2.06/0.56  fof(f82,plain,(
% 2.06/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 2.06/0.56    inference(cnf_transformation,[],[f38])).
% 2.06/0.56  fof(f38,plain,(
% 2.06/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.06/0.56    inference(flattening,[],[f37])).
% 2.06/0.56  fof(f37,plain,(
% 2.06/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.06/0.56    inference(ennf_transformation,[],[f16])).
% 2.06/0.56  fof(f16,axiom,(
% 2.06/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 2.06/0.56  fof(f2527,plain,(
% 2.06/0.56    ~spl4_146 | spl4_31 | ~spl4_113),
% 2.06/0.56    inference(avatar_split_clause,[],[f2505,f1973,f432,f2524])).
% 2.06/0.56  fof(f432,plain,(
% 2.06/0.56    spl4_31 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.06/0.56  fof(f2505,plain,(
% 2.06/0.56    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_31 | ~spl4_113)),
% 2.06/0.56    inference(backward_demodulation,[],[f434,f1974])).
% 2.06/0.56  fof(f434,plain,(
% 2.06/0.56    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_31),
% 2.06/0.56    inference(avatar_component_clause,[],[f432])).
% 2.06/0.56  fof(f2350,plain,(
% 2.06/0.56    spl4_138 | ~spl4_108 | ~spl4_136),
% 2.06/0.56    inference(avatar_split_clause,[],[f2271,f2255,f1922,f2348])).
% 2.06/0.56  fof(f1922,plain,(
% 2.06/0.56    spl4_108 <=> ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).
% 2.06/0.56  fof(f2255,plain,(
% 2.06/0.56    spl4_136 <=> v1_funct_1(k7_relat_1(sK3,sK2))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).
% 2.06/0.56  fof(f2271,plain,(
% 2.06/0.56    ( ! [X9] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9)))) ) | (~spl4_108 | ~spl4_136)),
% 2.06/0.56    inference(subsumption_resolution,[],[f2268,f1923])).
% 2.06/0.56  fof(f1923,plain,(
% 2.06/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_108),
% 2.06/0.56    inference(avatar_component_clause,[],[f1922])).
% 2.06/0.56  fof(f2268,plain,(
% 2.06/0.56    ( ! [X9] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X9) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X9))) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_136),
% 2.06/0.56    inference(resolution,[],[f2256,f91])).
% 2.06/0.56  fof(f91,plain,(
% 2.06/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.06/0.56    inference(cnf_transformation,[],[f44])).
% 2.06/0.56  fof(f44,plain,(
% 2.06/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.06/0.56    inference(flattening,[],[f43])).
% 2.06/0.56  fof(f43,plain,(
% 2.06/0.56    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.06/0.56    inference(ennf_transformation,[],[f24])).
% 2.06/0.56  fof(f24,axiom,(
% 2.06/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 2.06/0.56  fof(f2256,plain,(
% 2.06/0.56    v1_funct_1(k7_relat_1(sK3,sK2)) | ~spl4_136),
% 2.06/0.56    inference(avatar_component_clause,[],[f2255])).
% 2.06/0.56  fof(f2264,plain,(
% 2.06/0.56    ~spl4_1 | ~spl4_10 | spl4_136),
% 2.06/0.56    inference(avatar_contradiction_clause,[],[f2263])).
% 2.06/0.56  fof(f2263,plain,(
% 2.06/0.56    $false | (~spl4_1 | ~spl4_10 | spl4_136)),
% 2.06/0.56    inference(subsumption_resolution,[],[f2262,f181])).
% 2.06/0.56  fof(f2262,plain,(
% 2.06/0.56    ~v1_relat_1(sK3) | (~spl4_1 | spl4_136)),
% 2.06/0.56    inference(subsumption_resolution,[],[f2260,f125])).
% 2.06/0.56  fof(f125,plain,(
% 2.06/0.56    v1_funct_1(sK3) | ~spl4_1),
% 2.06/0.56    inference(avatar_component_clause,[],[f123])).
% 2.06/0.56  fof(f123,plain,(
% 2.06/0.56    spl4_1 <=> v1_funct_1(sK3)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.06/0.56  fof(f2260,plain,(
% 2.06/0.56    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl4_136),
% 2.06/0.56    inference(resolution,[],[f2257,f88])).
% 2.06/0.56  fof(f88,plain,(
% 2.06/0.56    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.56    inference(cnf_transformation,[],[f42])).
% 2.06/0.56  fof(f42,plain,(
% 2.06/0.56    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.56    inference(flattening,[],[f41])).
% 2.06/0.56  fof(f41,plain,(
% 2.06/0.56    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/0.56    inference(ennf_transformation,[],[f19])).
% 2.06/0.56  fof(f19,axiom,(
% 2.06/0.56    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.06/0.56  fof(f2257,plain,(
% 2.06/0.56    ~v1_funct_1(k7_relat_1(sK3,sK2)) | spl4_136),
% 2.06/0.56    inference(avatar_component_clause,[],[f2255])).
% 2.06/0.56  fof(f2258,plain,(
% 2.06/0.56    ~spl4_136 | ~spl4_5 | spl4_29 | ~spl4_44),
% 2.06/0.56    inference(avatar_split_clause,[],[f2244,f714,f424,f145,f2255])).
% 2.06/0.56  fof(f145,plain,(
% 2.06/0.56    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.06/0.56  fof(f424,plain,(
% 2.06/0.56    spl4_29 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.06/0.56  fof(f714,plain,(
% 2.06/0.56    spl4_44 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.06/0.56  fof(f2244,plain,(
% 2.06/0.56    ~v1_funct_1(k7_relat_1(sK3,sK2)) | (~spl4_5 | spl4_29 | ~spl4_44)),
% 2.06/0.56    inference(backward_demodulation,[],[f426,f1716])).
% 2.06/0.56  fof(f1716,plain,(
% 2.06/0.56    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | (~spl4_5 | ~spl4_44)),
% 2.06/0.56    inference(resolution,[],[f715,f147])).
% 2.06/0.56  fof(f147,plain,(
% 2.06/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_5),
% 2.06/0.56    inference(avatar_component_clause,[],[f145])).
% 2.06/0.56  fof(f715,plain,(
% 2.06/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2)) ) | ~spl4_44),
% 2.06/0.56    inference(avatar_component_clause,[],[f714])).
% 2.06/0.56  fof(f426,plain,(
% 2.06/0.56    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_29),
% 2.06/0.56    inference(avatar_component_clause,[],[f424])).
% 2.06/0.56  fof(f2248,plain,(
% 2.06/0.56    spl4_113 | ~spl4_5 | ~spl4_44),
% 2.06/0.56    inference(avatar_split_clause,[],[f1716,f714,f145,f1973])).
% 2.06/0.56  fof(f1924,plain,(
% 2.06/0.56    spl4_108 | ~spl4_33 | ~spl4_106),
% 2.06/0.56    inference(avatar_split_clause,[],[f1908,f1901,f475,f1922])).
% 2.06/0.56  fof(f475,plain,(
% 2.06/0.56    spl4_33 <=> ! [X7] : (v1_relat_1(X7) | ~r1_tarski(X7,sK3))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.06/0.56  fof(f1901,plain,(
% 2.06/0.56    spl4_106 <=> ! [X2] : r1_tarski(k7_relat_1(sK3,X2),sK3)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 2.06/0.56  fof(f1908,plain,(
% 2.06/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | (~spl4_33 | ~spl4_106)),
% 2.06/0.56    inference(resolution,[],[f1902,f476])).
% 2.06/0.56  fof(f476,plain,(
% 2.06/0.56    ( ! [X7] : (~r1_tarski(X7,sK3) | v1_relat_1(X7)) ) | ~spl4_33),
% 2.06/0.56    inference(avatar_component_clause,[],[f475])).
% 2.06/0.56  fof(f1902,plain,(
% 2.06/0.56    ( ! [X2] : (r1_tarski(k7_relat_1(sK3,X2),sK3)) ) | ~spl4_106),
% 2.06/0.56    inference(avatar_component_clause,[],[f1901])).
% 2.06/0.56  fof(f1903,plain,(
% 2.06/0.56    spl4_106 | ~spl4_103),
% 2.06/0.56    inference(avatar_split_clause,[],[f1899,f1844,f1901])).
% 2.06/0.56  fof(f1844,plain,(
% 2.06/0.56    spl4_103 <=> ! [X11,X10] : (r1_tarski(k7_relat_1(sK3,X10),X11) | ~r1_tarski(sK3,X11))),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_103])])).
% 2.06/0.56  fof(f1899,plain,(
% 2.06/0.56    ( ! [X2] : (r1_tarski(k7_relat_1(sK3,X2),sK3)) ) | ~spl4_103),
% 2.06/0.56    inference(resolution,[],[f1845,f113])).
% 2.06/0.56  fof(f113,plain,(
% 2.06/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.06/0.56    inference(equality_resolution,[],[f94])).
% 2.06/0.56  fof(f94,plain,(
% 2.06/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.06/0.56    inference(cnf_transformation,[],[f62])).
% 2.06/0.56  fof(f62,plain,(
% 2.06/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.56    inference(flattening,[],[f61])).
% 2.06/0.56  fof(f61,plain,(
% 2.06/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.56    inference(nnf_transformation,[],[f1])).
% 2.06/0.56  fof(f1,axiom,(
% 2.06/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.56  fof(f1845,plain,(
% 2.06/0.56    ( ! [X10,X11] : (~r1_tarski(sK3,X11) | r1_tarski(k7_relat_1(sK3,X10),X11)) ) | ~spl4_103),
% 2.06/0.56    inference(avatar_component_clause,[],[f1844])).
% 2.06/0.56  fof(f1857,plain,(
% 2.06/0.56    spl4_103 | ~spl4_10),
% 2.06/0.56    inference(avatar_split_clause,[],[f1540,f179,f1844])).
% 2.06/0.56  fof(f1540,plain,(
% 2.06/0.56    ( ! [X15,X16] : (r1_tarski(k7_relat_1(sK3,X15),X16) | ~r1_tarski(sK3,X16)) ) | ~spl4_10),
% 2.06/0.56    inference(resolution,[],[f181,f256])).
% 2.06/0.56  fof(f256,plain,(
% 2.06/0.56    ( ! [X14,X15,X13] : (~v1_relat_1(X13) | r1_tarski(k7_relat_1(X13,X15),X14) | ~r1_tarski(X13,X14)) )),
% 2.06/0.56    inference(resolution,[],[f111,f78])).
% 2.06/0.56  fof(f78,plain,(
% 2.06/0.56    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.06/0.56    inference(cnf_transformation,[],[f33])).
% 2.06/0.56  fof(f33,plain,(
% 2.06/0.56    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.06/0.56    inference(ennf_transformation,[],[f14])).
% 2.06/0.56  fof(f14,axiom,(
% 2.06/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 2.06/0.56  fof(f111,plain,(
% 2.06/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.06/0.56    inference(cnf_transformation,[],[f54])).
% 2.06/0.56  fof(f54,plain,(
% 2.06/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.06/0.56    inference(flattening,[],[f53])).
% 2.06/0.56  fof(f53,plain,(
% 2.06/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.06/0.56    inference(ennf_transformation,[],[f2])).
% 2.06/0.56  fof(f2,axiom,(
% 2.06/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.06/0.56  fof(f1574,plain,(
% 2.06/0.56    spl4_16 | ~spl4_5),
% 2.06/0.56    inference(avatar_split_clause,[],[f1566,f145,f260])).
% 2.06/0.56  fof(f260,plain,(
% 2.06/0.56    spl4_16 <=> v5_relat_1(sK3,sK1)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.06/0.56  fof(f1566,plain,(
% 2.06/0.56    v5_relat_1(sK3,sK1) | ~spl4_5),
% 2.06/0.56    inference(resolution,[],[f147,f104])).
% 2.06/0.56  fof(f104,plain,(
% 2.06/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.06/0.56    inference(cnf_transformation,[],[f50])).
% 2.06/0.56  fof(f50,plain,(
% 2.06/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.56    inference(ennf_transformation,[],[f20])).
% 2.06/0.56  fof(f20,axiom,(
% 2.06/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.06/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.06/0.56  fof(f1506,plain,(
% 2.06/0.56    ~spl4_7 | spl4_30 | ~spl4_49 | ~spl4_64 | ~spl4_70 | ~spl4_77),
% 2.06/0.56    inference(avatar_contradiction_clause,[],[f1505])).
% 2.06/0.56  fof(f1505,plain,(
% 2.06/0.56    $false | (~spl4_7 | spl4_30 | ~spl4_49 | ~spl4_64 | ~spl4_70 | ~spl4_77)),
% 2.06/0.56    inference(subsumption_resolution,[],[f1504,f825])).
% 2.06/0.56  fof(f825,plain,(
% 2.06/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_49),
% 2.06/0.56    inference(avatar_component_clause,[],[f824])).
% 2.06/0.56  fof(f824,plain,(
% 2.06/0.56    spl4_49 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 2.06/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.06/0.56  fof(f1504,plain,(
% 2.06/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl4_7 | spl4_30 | ~spl4_64 | ~spl4_70 | ~spl4_77)),
% 2.06/0.57    inference(forward_demodulation,[],[f1503,f1195])).
% 2.06/0.57  fof(f1195,plain,(
% 2.06/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2)) ) | ~spl4_77),
% 2.06/0.57    inference(avatar_component_clause,[],[f1194])).
% 2.06/0.57  fof(f1194,plain,(
% 2.06/0.57    spl4_77 <=> ! [X1,X0,X2] : k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 2.06/0.57  fof(f1503,plain,(
% 2.06/0.57    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | (~spl4_7 | spl4_30 | ~spl4_64 | ~spl4_70)),
% 2.06/0.57    inference(forward_demodulation,[],[f1450,f1086])).
% 2.06/0.57  fof(f1086,plain,(
% 2.06/0.57    k1_xboole_0 = sK3 | ~spl4_70),
% 2.06/0.57    inference(avatar_component_clause,[],[f1084])).
% 2.06/0.57  fof(f1084,plain,(
% 2.06/0.57    spl4_70 <=> k1_xboole_0 = sK3),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 2.06/0.57  fof(f1450,plain,(
% 2.06/0.57    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | (~spl4_7 | spl4_30 | ~spl4_64)),
% 2.06/0.57    inference(forward_demodulation,[],[f1449,f156])).
% 2.06/0.57  fof(f156,plain,(
% 2.06/0.57    k1_xboole_0 = sK0 | ~spl4_7),
% 2.06/0.57    inference(avatar_component_clause,[],[f154])).
% 2.06/0.57  fof(f154,plain,(
% 2.06/0.57    spl4_7 <=> k1_xboole_0 = sK0),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.06/0.57  fof(f1449,plain,(
% 2.06/0.57    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_30 | ~spl4_64)),
% 2.06/0.57    inference(forward_demodulation,[],[f430,f1002])).
% 2.06/0.57  fof(f1002,plain,(
% 2.06/0.57    k1_xboole_0 = sK2 | ~spl4_64),
% 2.06/0.57    inference(avatar_component_clause,[],[f1000])).
% 2.06/0.57  fof(f1000,plain,(
% 2.06/0.57    spl4_64 <=> k1_xboole_0 = sK2),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 2.06/0.57  fof(f1196,plain,(
% 2.06/0.57    spl4_77 | ~spl4_13 | ~spl4_75),
% 2.06/0.57    inference(avatar_split_clause,[],[f1149,f1141,f204,f1194])).
% 2.06/0.57  fof(f204,plain,(
% 2.06/0.57    spl4_13 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.06/0.57  fof(f1141,plain,(
% 2.06/0.57    spl4_75 <=> ! [X7,X8,X6] : (k1_xboole_0 = k2_partfun1(X6,X7,k1_xboole_0,X8) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))))),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 2.06/0.57  fof(f1149,plain,(
% 2.06/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2)) ) | (~spl4_13 | ~spl4_75)),
% 2.06/0.57    inference(subsumption_resolution,[],[f1146,f205])).
% 2.06/0.57  fof(f205,plain,(
% 2.06/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_13),
% 2.06/0.57    inference(avatar_component_clause,[],[f204])).
% 2.06/0.57  fof(f1146,plain,(
% 2.06/0.57    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_partfun1(X0,X1,k1_xboole_0,X2) | ~r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1))) ) | ~spl4_75),
% 2.06/0.57    inference(resolution,[],[f1142,f97])).
% 2.06/0.57  fof(f97,plain,(
% 2.06/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f63])).
% 2.06/0.57  fof(f63,plain,(
% 2.06/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.06/0.57    inference(nnf_transformation,[],[f5])).
% 2.06/0.57  fof(f5,axiom,(
% 2.06/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.06/0.57  fof(f1142,plain,(
% 2.06/0.57    ( ! [X6,X8,X7] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_xboole_0 = k2_partfun1(X6,X7,k1_xboole_0,X8)) ) | ~spl4_75),
% 2.06/0.57    inference(avatar_component_clause,[],[f1141])).
% 2.06/0.57  fof(f1143,plain,(
% 2.06/0.57    spl4_75 | ~spl4_9 | ~spl4_71),
% 2.06/0.57    inference(avatar_split_clause,[],[f1106,f1090,f172,f1141])).
% 2.06/0.57  fof(f172,plain,(
% 2.06/0.57    spl4_9 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.06/0.57  fof(f1090,plain,(
% 2.06/0.57    spl4_71 <=> v1_funct_1(k1_xboole_0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 2.06/0.57  fof(f1106,plain,(
% 2.06/0.57    ( ! [X6,X8,X7] : (k1_xboole_0 = k2_partfun1(X6,X7,k1_xboole_0,X8) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | (~spl4_9 | ~spl4_71)),
% 2.06/0.57    inference(forward_demodulation,[],[f1096,f173])).
% 2.06/0.57  fof(f173,plain,(
% 2.06/0.57    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl4_9),
% 2.06/0.57    inference(avatar_component_clause,[],[f172])).
% 2.06/0.57  fof(f1096,plain,(
% 2.06/0.57    ( ! [X6,X8,X7] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k2_partfun1(X6,X7,k1_xboole_0,X8) = k7_relat_1(k1_xboole_0,X8)) ) | ~spl4_71),
% 2.06/0.57    inference(resolution,[],[f1092,f112])).
% 2.06/0.57  fof(f112,plain,(
% 2.06/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f56])).
% 2.06/0.57  fof(f56,plain,(
% 2.06/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.06/0.57    inference(flattening,[],[f55])).
% 2.06/0.57  fof(f55,plain,(
% 2.06/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.06/0.57    inference(ennf_transformation,[],[f23])).
% 2.06/0.57  fof(f23,axiom,(
% 2.06/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.06/0.57  fof(f1092,plain,(
% 2.06/0.57    v1_funct_1(k1_xboole_0) | ~spl4_71),
% 2.06/0.57    inference(avatar_component_clause,[],[f1090])).
% 2.06/0.57  fof(f1093,plain,(
% 2.06/0.57    spl4_71 | ~spl4_1 | ~spl4_60),
% 2.06/0.57    inference(avatar_split_clause,[],[f1073,f978,f123,f1090])).
% 2.06/0.57  fof(f978,plain,(
% 2.06/0.57    spl4_60 <=> r1_tarski(sK3,k1_xboole_0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 2.06/0.57  fof(f1073,plain,(
% 2.06/0.57    v1_funct_1(k1_xboole_0) | (~spl4_1 | ~spl4_60)),
% 2.06/0.57    inference(backward_demodulation,[],[f125,f1016])).
% 2.06/0.57  fof(f1016,plain,(
% 2.06/0.57    k1_xboole_0 = sK3 | ~spl4_60),
% 2.06/0.57    inference(resolution,[],[f980,f75])).
% 2.06/0.57  fof(f75,plain,(
% 2.06/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.06/0.57    inference(cnf_transformation,[],[f31])).
% 2.06/0.57  fof(f31,plain,(
% 2.06/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.06/0.57    inference(ennf_transformation,[],[f3])).
% 2.06/0.57  fof(f3,axiom,(
% 2.06/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.06/0.57  fof(f980,plain,(
% 2.06/0.57    r1_tarski(sK3,k1_xboole_0) | ~spl4_60),
% 2.06/0.57    inference(avatar_component_clause,[],[f978])).
% 2.06/0.57  fof(f1087,plain,(
% 2.06/0.57    spl4_70 | ~spl4_60),
% 2.06/0.57    inference(avatar_split_clause,[],[f1016,f978,f1084])).
% 2.06/0.57  fof(f1003,plain,(
% 2.06/0.57    spl4_64 | ~spl4_55),
% 2.06/0.57    inference(avatar_split_clause,[],[f923,f918,f1000])).
% 2.06/0.57  fof(f918,plain,(
% 2.06/0.57    spl4_55 <=> r1_tarski(sK2,k1_xboole_0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 2.06/0.57  fof(f923,plain,(
% 2.06/0.57    k1_xboole_0 = sK2 | ~spl4_55),
% 2.06/0.57    inference(resolution,[],[f920,f75])).
% 2.06/0.57  fof(f920,plain,(
% 2.06/0.57    r1_tarski(sK2,k1_xboole_0) | ~spl4_55),
% 2.06/0.57    inference(avatar_component_clause,[],[f918])).
% 2.06/0.57  fof(f981,plain,(
% 2.06/0.57    spl4_60 | ~spl4_6 | ~spl4_8),
% 2.06/0.57    inference(avatar_split_clause,[],[f903,f163,f150,f978])).
% 2.06/0.57  fof(f163,plain,(
% 2.06/0.57    spl4_8 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.06/0.57  fof(f903,plain,(
% 2.06/0.57    r1_tarski(sK3,k1_xboole_0) | (~spl4_6 | ~spl4_8)),
% 2.06/0.57    inference(forward_demodulation,[],[f897,f115])).
% 2.06/0.57  fof(f115,plain,(
% 2.06/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.06/0.57    inference(equality_resolution,[],[f100])).
% 2.06/0.57  fof(f100,plain,(
% 2.06/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.06/0.57    inference(cnf_transformation,[],[f65])).
% 2.06/0.57  fof(f65,plain,(
% 2.06/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.06/0.57    inference(flattening,[],[f64])).
% 2.06/0.57  fof(f64,plain,(
% 2.06/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.06/0.57    inference(nnf_transformation,[],[f4])).
% 2.06/0.57  fof(f4,axiom,(
% 2.06/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.06/0.57  fof(f897,plain,(
% 2.06/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl4_6 | ~spl4_8)),
% 2.06/0.57    inference(backward_demodulation,[],[f165,f151])).
% 2.06/0.57  fof(f151,plain,(
% 2.06/0.57    k1_xboole_0 = sK1 | ~spl4_6),
% 2.06/0.57    inference(avatar_component_clause,[],[f150])).
% 2.06/0.57  fof(f165,plain,(
% 2.06/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_8),
% 2.06/0.57    inference(avatar_component_clause,[],[f163])).
% 2.06/0.57  fof(f921,plain,(
% 2.06/0.57    spl4_55 | ~spl4_2 | ~spl4_7),
% 2.06/0.57    inference(avatar_split_clause,[],[f904,f154,f128,f918])).
% 2.06/0.57  fof(f904,plain,(
% 2.06/0.57    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_7)),
% 2.06/0.57    inference(backward_demodulation,[],[f130,f156])).
% 2.06/0.57  fof(f890,plain,(
% 2.06/0.57    sK3 != k7_relat_1(sK3,sK0) | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK3)),
% 2.06/0.57    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.57  fof(f844,plain,(
% 2.06/0.57    spl4_52 | ~spl4_10 | ~spl4_18),
% 2.06/0.57    inference(avatar_split_clause,[],[f652,f284,f179,f842])).
% 2.06/0.57  fof(f284,plain,(
% 2.06/0.57    spl4_18 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.06/0.57  fof(f652,plain,(
% 2.06/0.57    ( ! [X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1)) ) | (~spl4_10 | ~spl4_18)),
% 2.06/0.57    inference(subsumption_resolution,[],[f649,f181])).
% 2.06/0.57  fof(f649,plain,(
% 2.06/0.57    ( ! [X3] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X3)),sK1) | ~v1_relat_1(sK3)) ) | ~spl4_18),
% 2.06/0.57    inference(resolution,[],[f255,f286])).
% 2.06/0.57  fof(f286,plain,(
% 2.06/0.57    r1_tarski(k2_relat_1(sK3),sK1) | ~spl4_18),
% 2.06/0.57    inference(avatar_component_clause,[],[f284])).
% 2.06/0.57  fof(f255,plain,(
% 2.06/0.57    ( ! [X12,X10,X11] : (~r1_tarski(k2_relat_1(X10),X11) | r1_tarski(k2_relat_1(k7_relat_1(X10,X12)),X11) | ~v1_relat_1(X10)) )),
% 2.06/0.57    inference(resolution,[],[f111,f80])).
% 2.06/0.57  fof(f80,plain,(
% 2.06/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f35])).
% 2.06/0.57  fof(f35,plain,(
% 2.06/0.57    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.06/0.57    inference(ennf_transformation,[],[f18])).
% 2.06/0.57  fof(f18,axiom,(
% 2.06/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 2.06/0.57  fof(f826,plain,(
% 2.06/0.57    spl4_49 | ~spl4_21 | ~spl4_47),
% 2.06/0.57    inference(avatar_split_clause,[],[f814,f803,f309,f824])).
% 2.06/0.57  fof(f309,plain,(
% 2.06/0.57    spl4_21 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.06/0.57  fof(f803,plain,(
% 2.06/0.57    spl4_47 <=> ! [X0] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 2.06/0.57  fof(f814,plain,(
% 2.06/0.57    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl4_21 | ~spl4_47)),
% 2.06/0.57    inference(subsumption_resolution,[],[f813,f310])).
% 2.06/0.57  fof(f310,plain,(
% 2.06/0.57    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_21),
% 2.06/0.57    inference(avatar_component_clause,[],[f309])).
% 2.06/0.57  fof(f813,plain,(
% 2.06/0.57    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_47),
% 2.06/0.57    inference(trivial_inequality_removal,[],[f810])).
% 2.06/0.57  fof(f810,plain,(
% 2.06/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_47),
% 2.06/0.57    inference(superposition,[],[f353,f804])).
% 2.06/0.57  fof(f804,plain,(
% 2.06/0.57    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl4_47),
% 2.06/0.57    inference(avatar_component_clause,[],[f803])).
% 2.06/0.57  fof(f353,plain,(
% 2.06/0.57    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 2.06/0.57    inference(forward_demodulation,[],[f120,f116])).
% 2.06/0.57  fof(f116,plain,(
% 2.06/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.06/0.57    inference(equality_resolution,[],[f99])).
% 2.06/0.57  fof(f99,plain,(
% 2.06/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.06/0.57    inference(cnf_transformation,[],[f65])).
% 2.06/0.57  fof(f120,plain,(
% 2.06/0.57    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.06/0.57    inference(equality_resolution,[],[f108])).
% 2.06/0.57  fof(f108,plain,(
% 2.06/0.57    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.57    inference(cnf_transformation,[],[f66])).
% 2.06/0.57  fof(f805,plain,(
% 2.06/0.57    spl4_47 | ~spl4_12 | ~spl4_21),
% 2.06/0.57    inference(avatar_split_clause,[],[f607,f309,f199,f803])).
% 2.06/0.57  fof(f199,plain,(
% 2.06/0.57    spl4_12 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.06/0.57  fof(f607,plain,(
% 2.06/0.57    ( ! [X0] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | (~spl4_12 | ~spl4_21)),
% 2.06/0.57    inference(forward_demodulation,[],[f605,f201])).
% 2.06/0.57  fof(f201,plain,(
% 2.06/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_12),
% 2.06/0.57    inference(avatar_component_clause,[],[f199])).
% 2.06/0.57  fof(f605,plain,(
% 2.06/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl4_21),
% 2.06/0.57    inference(resolution,[],[f295,f310])).
% 2.06/0.57  fof(f295,plain,(
% 2.06/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_relset_1(k1_xboole_0,X2,X3) = k1_relat_1(X3)) )),
% 2.06/0.57    inference(superposition,[],[f102,f116])).
% 2.06/0.57  fof(f752,plain,(
% 2.06/0.57    spl4_45 | ~spl4_10),
% 2.06/0.57    inference(avatar_split_clause,[],[f502,f179,f749])).
% 2.06/0.57  fof(f749,plain,(
% 2.06/0.57    spl4_45 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.06/0.57  fof(f502,plain,(
% 2.06/0.57    k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | ~spl4_10),
% 2.06/0.57    inference(resolution,[],[f183,f181])).
% 2.06/0.57  fof(f183,plain,(
% 2.06/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0))) )),
% 2.06/0.57    inference(resolution,[],[f79,f75])).
% 2.06/0.57  fof(f79,plain,(
% 2.06/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f34])).
% 2.06/0.57  fof(f34,plain,(
% 2.06/0.57    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.06/0.57    inference(ennf_transformation,[],[f13])).
% 2.06/0.57  fof(f13,axiom,(
% 2.06/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 2.06/0.57  fof(f716,plain,(
% 2.06/0.57    spl4_44 | ~spl4_1),
% 2.06/0.57    inference(avatar_split_clause,[],[f372,f123,f714])).
% 2.06/0.57  fof(f372,plain,(
% 2.06/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK3,X2) = k2_partfun1(X0,X1,sK3,X2)) ) | ~spl4_1),
% 2.06/0.57    inference(resolution,[],[f112,f125])).
% 2.06/0.57  fof(f477,plain,(
% 2.06/0.57    spl4_33 | ~spl4_10),
% 2.06/0.57    inference(avatar_split_clause,[],[f473,f179,f475])).
% 2.06/0.57  fof(f473,plain,(
% 2.06/0.57    ( ! [X7] : (v1_relat_1(X7) | ~r1_tarski(X7,sK3)) ) | ~spl4_10),
% 2.06/0.57    inference(resolution,[],[f176,f181])).
% 2.06/0.57  fof(f176,plain,(
% 2.06/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(X0) | ~r1_tarski(X0,X1)) )),
% 2.06/0.57    inference(resolution,[],[f74,f97])).
% 2.06/0.57  fof(f74,plain,(
% 2.06/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f30])).
% 2.06/0.57  fof(f30,plain,(
% 2.06/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.06/0.57    inference(ennf_transformation,[],[f6])).
% 2.06/0.57  fof(f6,axiom,(
% 2.06/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.06/0.57  fof(f435,plain,(
% 2.06/0.57    ~spl4_29 | ~spl4_30 | ~spl4_31),
% 2.06/0.57    inference(avatar_split_clause,[],[f72,f432,f428,f424])).
% 2.06/0.57  fof(f72,plain,(
% 2.06/0.57    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 2.06/0.57    inference(cnf_transformation,[],[f58])).
% 2.06/0.57  fof(f58,plain,(
% 2.06/0.57    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.06/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f57])).
% 2.06/0.57  fof(f57,plain,(
% 2.06/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.06/0.57    introduced(choice_axiom,[])).
% 2.06/0.57  fof(f28,plain,(
% 2.06/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.06/0.57    inference(flattening,[],[f27])).
% 2.06/0.57  fof(f27,plain,(
% 2.06/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.06/0.57    inference(ennf_transformation,[],[f26])).
% 2.06/0.57  fof(f26,negated_conjecture,(
% 2.06/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.06/0.57    inference(negated_conjecture,[],[f25])).
% 2.06/0.57  fof(f25,conjecture,(
% 2.06/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 2.06/0.57  fof(f391,plain,(
% 2.06/0.57    spl4_28 | ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_26),
% 2.06/0.57    inference(avatar_split_clause,[],[f379,f368,f150,f145,f133,f388])).
% 2.06/0.57  fof(f133,plain,(
% 2.06/0.57    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.06/0.57  fof(f368,plain,(
% 2.06/0.57    spl4_26 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.06/0.57  fof(f379,plain,(
% 2.06/0.57    sK0 = k1_relat_1(sK3) | (~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_26)),
% 2.06/0.57    inference(backward_demodulation,[],[f370,f378])).
% 2.06/0.57  fof(f378,plain,(
% 2.06/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | ~spl4_5 | spl4_6)),
% 2.06/0.57    inference(subsumption_resolution,[],[f377,f147])).
% 2.06/0.57  fof(f377,plain,(
% 2.06/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | spl4_6)),
% 2.06/0.57    inference(subsumption_resolution,[],[f374,f152])).
% 2.06/0.57  fof(f374,plain,(
% 2.06/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 2.06/0.57    inference(resolution,[],[f105,f135])).
% 2.06/0.57  fof(f135,plain,(
% 2.06/0.57    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 2.06/0.57    inference(avatar_component_clause,[],[f133])).
% 2.06/0.57  fof(f105,plain,(
% 2.06/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.57    inference(cnf_transformation,[],[f66])).
% 2.06/0.57  fof(f370,plain,(
% 2.06/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_26),
% 2.06/0.57    inference(avatar_component_clause,[],[f368])).
% 2.06/0.57  fof(f371,plain,(
% 2.06/0.57    spl4_26 | ~spl4_5),
% 2.06/0.57    inference(avatar_split_clause,[],[f292,f145,f368])).
% 2.06/0.57  fof(f292,plain,(
% 2.06/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_5),
% 2.06/0.57    inference(resolution,[],[f102,f147])).
% 2.06/0.57  fof(f317,plain,(
% 2.06/0.57    ~spl4_13 | spl4_21),
% 2.06/0.57    inference(avatar_contradiction_clause,[],[f316])).
% 2.06/0.57  fof(f316,plain,(
% 2.06/0.57    $false | (~spl4_13 | spl4_21)),
% 2.06/0.57    inference(subsumption_resolution,[],[f314,f205])).
% 2.06/0.57  fof(f314,plain,(
% 2.06/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_21),
% 2.06/0.57    inference(resolution,[],[f311,f97])).
% 2.06/0.57  fof(f311,plain,(
% 2.06/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_21),
% 2.06/0.57    inference(avatar_component_clause,[],[f309])).
% 2.06/0.57  fof(f304,plain,(
% 2.06/0.57    spl4_19 | ~spl4_10 | ~spl4_15),
% 2.06/0.57    inference(avatar_split_clause,[],[f266,f241,f179,f301])).
% 2.06/0.57  fof(f301,plain,(
% 2.06/0.57    spl4_19 <=> sK3 = k7_relat_1(sK3,sK0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.06/0.57  fof(f241,plain,(
% 2.06/0.57    spl4_15 <=> v4_relat_1(sK3,sK0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.06/0.57  fof(f266,plain,(
% 2.06/0.57    sK3 = k7_relat_1(sK3,sK0) | (~spl4_10 | ~spl4_15)),
% 2.06/0.57    inference(subsumption_resolution,[],[f265,f181])).
% 2.06/0.57  fof(f265,plain,(
% 2.06/0.57    sK3 = k7_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_15),
% 2.06/0.57    inference(resolution,[],[f92,f243])).
% 2.06/0.57  fof(f243,plain,(
% 2.06/0.57    v4_relat_1(sK3,sK0) | ~spl4_15),
% 2.06/0.57    inference(avatar_component_clause,[],[f241])).
% 2.06/0.57  fof(f92,plain,(
% 2.06/0.57    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f46])).
% 2.06/0.57  fof(f46,plain,(
% 2.06/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.06/0.57    inference(flattening,[],[f45])).
% 2.06/0.57  fof(f45,plain,(
% 2.06/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.06/0.57    inference(ennf_transformation,[],[f12])).
% 2.06/0.57  fof(f12,axiom,(
% 2.06/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.06/0.57  fof(f287,plain,(
% 2.06/0.57    spl4_18 | ~spl4_10 | ~spl4_16),
% 2.06/0.57    inference(avatar_split_clause,[],[f268,f260,f179,f284])).
% 2.06/0.57  fof(f268,plain,(
% 2.06/0.57    r1_tarski(k2_relat_1(sK3),sK1) | (~spl4_10 | ~spl4_16)),
% 2.06/0.57    inference(subsumption_resolution,[],[f267,f181])).
% 2.06/0.57  fof(f267,plain,(
% 2.06/0.57    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl4_16),
% 2.06/0.57    inference(resolution,[],[f262,f83])).
% 2.06/0.57  fof(f83,plain,(
% 2.06/0.57    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f59])).
% 2.06/0.57  fof(f59,plain,(
% 2.06/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.06/0.57    inference(nnf_transformation,[],[f39])).
% 2.06/0.57  fof(f39,plain,(
% 2.06/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.06/0.57    inference(ennf_transformation,[],[f8])).
% 2.06/0.57  fof(f8,axiom,(
% 2.06/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 2.06/0.57  fof(f262,plain,(
% 2.06/0.57    v5_relat_1(sK3,sK1) | ~spl4_16),
% 2.06/0.57    inference(avatar_component_clause,[],[f260])).
% 2.06/0.57  fof(f244,plain,(
% 2.06/0.57    spl4_15 | ~spl4_5),
% 2.06/0.57    inference(avatar_split_clause,[],[f236,f145,f241])).
% 2.06/0.57  fof(f236,plain,(
% 2.06/0.57    v4_relat_1(sK3,sK0) | ~spl4_5),
% 2.06/0.57    inference(resolution,[],[f103,f147])).
% 2.06/0.57  fof(f103,plain,(
% 2.06/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f50])).
% 2.06/0.57  fof(f206,plain,(
% 2.06/0.57    spl4_13 | ~spl4_11),
% 2.06/0.57    inference(avatar_split_clause,[],[f197,f191,f204])).
% 2.06/0.57  fof(f191,plain,(
% 2.06/0.57    spl4_11 <=> ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.06/0.57  fof(f197,plain,(
% 2.06/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_11),
% 2.06/0.57    inference(backward_demodulation,[],[f192,f195])).
% 2.06/0.57  fof(f195,plain,(
% 2.06/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_11),
% 2.06/0.57    inference(resolution,[],[f192,f75])).
% 2.06/0.57  fof(f192,plain,(
% 2.06/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | ~spl4_11),
% 2.06/0.57    inference(avatar_component_clause,[],[f191])).
% 2.06/0.57  fof(f202,plain,(
% 2.06/0.57    spl4_12 | ~spl4_11),
% 2.06/0.57    inference(avatar_split_clause,[],[f195,f191,f199])).
% 2.06/0.57  fof(f193,plain,(
% 2.06/0.57    spl4_11 | ~spl4_4 | ~spl4_9),
% 2.06/0.57    inference(avatar_split_clause,[],[f188,f172,f139,f191])).
% 2.06/0.57  fof(f139,plain,(
% 2.06/0.57    spl4_4 <=> v1_relat_1(k1_xboole_0)),
% 2.06/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.06/0.57  fof(f188,plain,(
% 2.06/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | (~spl4_4 | ~spl4_9)),
% 2.06/0.57    inference(subsumption_resolution,[],[f185,f141])).
% 2.06/0.57  fof(f141,plain,(
% 2.06/0.57    v1_relat_1(k1_xboole_0) | ~spl4_4),
% 2.06/0.57    inference(avatar_component_clause,[],[f139])).
% 2.06/0.57  fof(f185,plain,(
% 2.06/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_9),
% 2.06/0.57    inference(superposition,[],[f79,f173])).
% 2.06/0.57  fof(f182,plain,(
% 2.06/0.57    spl4_10 | ~spl4_5),
% 2.06/0.57    inference(avatar_split_clause,[],[f177,f145,f179])).
% 2.06/0.57  fof(f177,plain,(
% 2.06/0.57    v1_relat_1(sK3) | ~spl4_5),
% 2.06/0.57    inference(subsumption_resolution,[],[f175,f76])).
% 2.06/0.57  fof(f76,plain,(
% 2.06/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.06/0.57    inference(cnf_transformation,[],[f10])).
% 2.06/0.57  fof(f10,axiom,(
% 2.06/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.06/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.06/0.57  fof(f175,plain,(
% 2.06/0.57    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 2.06/0.57    inference(resolution,[],[f74,f147])).
% 2.06/0.57  fof(f174,plain,(
% 2.06/0.57    spl4_9 | ~spl4_4),
% 2.06/0.57    inference(avatar_split_clause,[],[f160,f139,f172])).
% 2.06/0.57  fof(f160,plain,(
% 2.06/0.57    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl4_4),
% 2.06/0.57    inference(subsumption_resolution,[],[f159,f141])).
% 2.06/0.57  fof(f159,plain,(
% 2.06/0.57    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 2.06/0.57    inference(resolution,[],[f78,f75])).
% 2.06/0.57  fof(f166,plain,(
% 2.06/0.57    spl4_8 | ~spl4_5),
% 2.06/0.57    inference(avatar_split_clause,[],[f161,f145,f163])).
% 2.06/0.57  fof(f161,plain,(
% 2.06/0.57    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_5),
% 2.06/0.57    inference(resolution,[],[f96,f147])).
% 2.06/0.57  fof(f96,plain,(
% 2.06/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.06/0.57    inference(cnf_transformation,[],[f63])).
% 2.06/0.57  fof(f157,plain,(
% 2.06/0.57    ~spl4_6 | spl4_7),
% 2.06/0.57    inference(avatar_split_clause,[],[f71,f154,f150])).
% 2.06/0.57  fof(f71,plain,(
% 2.06/0.57    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.06/0.57    inference(cnf_transformation,[],[f58])).
% 2.06/0.57  fof(f148,plain,(
% 2.06/0.57    spl4_5),
% 2.06/0.57    inference(avatar_split_clause,[],[f69,f145])).
% 2.06/0.57  fof(f69,plain,(
% 2.06/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.57    inference(cnf_transformation,[],[f58])).
% 2.06/0.57  fof(f142,plain,(
% 2.06/0.57    spl4_4),
% 2.06/0.57    inference(avatar_split_clause,[],[f137,f139])).
% 2.06/0.57  fof(f137,plain,(
% 2.06/0.57    v1_relat_1(k1_xboole_0)),
% 2.06/0.57    inference(superposition,[],[f76,f115])).
% 2.06/0.57  fof(f136,plain,(
% 2.06/0.57    spl4_3),
% 2.06/0.57    inference(avatar_split_clause,[],[f68,f133])).
% 2.06/0.57  fof(f68,plain,(
% 2.06/0.57    v1_funct_2(sK3,sK0,sK1)),
% 2.06/0.57    inference(cnf_transformation,[],[f58])).
% 2.06/0.57  fof(f131,plain,(
% 2.06/0.57    spl4_2),
% 2.06/0.57    inference(avatar_split_clause,[],[f70,f128])).
% 2.06/0.57  fof(f70,plain,(
% 2.06/0.57    r1_tarski(sK2,sK0)),
% 2.06/0.57    inference(cnf_transformation,[],[f58])).
% 2.06/0.57  fof(f126,plain,(
% 2.06/0.57    spl4_1),
% 2.06/0.57    inference(avatar_split_clause,[],[f67,f123])).
% 2.06/0.57  fof(f67,plain,(
% 2.06/0.57    v1_funct_1(sK3)),
% 2.06/0.57    inference(cnf_transformation,[],[f58])).
% 2.06/0.57  % SZS output end Proof for theBenchmark
% 2.06/0.57  % (25287)------------------------------
% 2.06/0.57  % (25287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.57  % (25287)Termination reason: Refutation
% 2.06/0.57  
% 2.06/0.57  % (25287)Memory used [KB]: 8059
% 2.06/0.57  % (25287)Time elapsed: 0.247 s
% 2.06/0.57  % (25287)------------------------------
% 2.06/0.57  % (25287)------------------------------
% 2.06/0.57  % (25284)Success in time 0.305 s
%------------------------------------------------------------------------------
