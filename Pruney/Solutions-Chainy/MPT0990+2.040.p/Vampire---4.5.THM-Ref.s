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
% DateTime   : Thu Dec  3 13:02:35 EST 2020

% Result     : Theorem 2.25s
% Output     : Refutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 501 expanded)
%              Number of leaves         :   48 ( 212 expanded)
%              Depth                    :   16
%              Number of atoms          : 1078 (2630 expanded)
%              Number of equality atoms :  247 ( 744 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f151,f160,f165,f188,f211,f218,f228,f246,f261,f361,f395,f399,f416,f448,f476,f495,f550,f565,f611,f629])).

fof(f629,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_26
    | ~ spl4_37
    | ~ spl4_53 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_26
    | ~ spl4_37
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f627,f258])).

fof(f258,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_26
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f627,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f626,f372])).

fof(f372,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl4_37
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f626,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_53 ),
    inference(trivial_inequality_removal,[],[f625])).

fof(f625,plain,
    ( k6_relat_1(sK1) != k6_relat_1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f624,f185])).

fof(f185,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f624,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f623,f164])).

fof(f164,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f623,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f622,f144])).

fof(f144,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f622,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f621,f159])).

fof(f159,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f621,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f620,f129])).

fof(f129,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f620,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f619,f104])).

fof(f104,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f619,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f614,f89])).

fof(f89,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f614,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_53 ),
    inference(superposition,[],[f58,f610])).

fof(f610,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl4_53
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f611,plain,
    ( spl4_53
    | ~ spl4_39
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f606,f562,f390,f608])).

fof(f390,plain,
    ( spl4_39
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f562,plain,
    ( spl4_50
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f606,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_39
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f392,f564])).

fof(f564,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f562])).

fof(f392,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f390])).

fof(f565,plain,
    ( ~ spl4_24
    | spl4_50
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f560,f454,f370,f223,f183,f162,f157,f142,f127,f562,f240])).

fof(f240,plain,
    ( spl4_24
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f223,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f454,plain,
    ( spl4_46
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f560,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f559,f185])).

fof(f559,plain,
    ( sK1 != k2_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f558,f225])).

fof(f225,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f223])).

fof(f558,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(trivial_inequality_removal,[],[f557])).

fof(f557,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_37
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f556,f372])).

fof(f556,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f555,f159])).

fof(f555,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f554,f129])).

fof(f554,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f553,f164])).

fof(f553,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f548,f144])).

fof(f548,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f58,f456])).

fof(f456,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f454])).

fof(f550,plain,
    ( spl4_40
    | ~ spl4_46 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | spl4_40
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f545,f67])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f545,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | spl4_40
    | ~ spl4_46 ),
    inference(backward_demodulation,[],[f415,f456])).

fof(f415,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl4_40
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f495,plain,
    ( spl4_46
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f494,f445,f142,f132,f127,f117,f454])).

fof(f117,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f132,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f445,plain,
    ( spl4_44
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f494,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f493,f144])).

fof(f493,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f492,f134])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f492,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f491,f129])).

fof(f491,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f483,f119])).

fof(f119,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f483,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_44 ),
    inference(superposition,[],[f75,f447])).

fof(f447,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f445])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f476,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_43 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_43 ),
    inference(subsumption_resolution,[],[f474,f144])).

fof(f474,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_43 ),
    inference(subsumption_resolution,[],[f473,f134])).

fof(f473,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_43 ),
    inference(subsumption_resolution,[],[f472,f129])).

fof(f472,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_43 ),
    inference(subsumption_resolution,[],[f469,f119])).

fof(f469,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_43 ),
    inference(resolution,[],[f443,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f443,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl4_43
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f448,plain,
    ( ~ spl4_43
    | spl4_44
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f437,f148,f445,f441])).

fof(f148,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f437,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f249,f150])).

fof(f150,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f249,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f68,f152])).

fof(f152,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f71,f72])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f416,plain,
    ( ~ spl4_40
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f411,f244,f183,f162,f142,f413])).

fof(f244,plain,
    ( spl4_25
  <=> ! [X0] :
        ( k2_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f411,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f410,f144])).

fof(f410,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f409,f164])).

fof(f409,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(trivial_inequality_removal,[],[f407])).

fof(f407,plain,
    ( sK1 != sK1
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_18
    | ~ spl4_25 ),
    inference(superposition,[],[f245,f185])).

fof(f245,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK3)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f244])).

fof(f399,plain,
    ( spl4_39
    | ~ spl4_24
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f398,f358,f127,f122,f117,f97,f240,f390])).

fof(f97,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f122,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f358,plain,
    ( spl4_36
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f398,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f397,f129])).

fof(f397,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f396,f124])).

fof(f124,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f396,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f384,f119])).

fof(f384,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f366,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f366,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f364])).

fof(f364,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_36 ),
    inference(superposition,[],[f286,f360])).

fof(f360,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f358])).

fof(f286,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f56,f72])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f395,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f394,f358,f117,f370])).

fof(f394,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f365,f119])).

fof(f365,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_36 ),
    inference(superposition,[],[f76,f360])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f361,plain,
    ( spl4_36
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f356,f148,f142,f137,f132,f127,f122,f117,f358])).

fof(f137,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f356,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f355,f129])).

fof(f355,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f354,f124])).

fof(f354,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f353,f119])).

fof(f353,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f352,f144])).

fof(f352,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f351,f139])).

fof(f139,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f351,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f348,f134])).

fof(f348,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f347,f150])).

fof(f347,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f70,f72])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f261,plain,
    ( spl4_26
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f260,f215,f132,f256])).

fof(f215,plain,
    ( spl4_22
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f260,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f252,f134])).

fof(f252,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_22 ),
    inference(superposition,[],[f78,f217])).

fof(f217,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f215])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f246,plain,
    ( spl4_24
    | spl4_25
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f238,f223,f157,f127,f244,f240])).

fof(f238,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X0,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f237,f159])).

fof(f237,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X0,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_9
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f236,f129])).

fof(f236,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != sK1
        | v2_funct_1(sK3)
        | ~ v2_funct_1(k5_relat_1(X0,sK3))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_23 ),
    inference(superposition,[],[f66,f225])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f228,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f227,f208,f117,f223])).

fof(f208,plain,
    ( spl4_21
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f227,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f220,f119])).

fof(f220,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_21 ),
    inference(superposition,[],[f78,f210])).

fof(f210,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f208])).

fof(f218,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f213,f137,f132,f92,f215])).

fof(f92,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f213,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_2
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f212,f94])).

fof(f94,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f212,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f203,f139])).

fof(f203,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f59,f134])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f211,plain,
    ( spl4_21
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f206,f122,f117,f97,f208])).

fof(f206,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f205,f99])).

fof(f205,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f202,f124])).

fof(f202,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f59,f119])).

fof(f188,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f187,f132,f112,f183])).

fof(f112,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f187,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f180,f134])).

fof(f180,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f114,f76])).

fof(f114,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f165,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f154,f132,f162])).

fof(f154,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f77,f134])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f160,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f153,f117,f157])).

fof(f153,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f77,f119])).

fof(f151,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f146,f107,f148])).

fof(f107,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f146,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f109,f72])).

fof(f109,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f145,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f44,f142])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f140,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f45,f137])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f135,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f46,f132])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f130,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f48,f122])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f49,f117])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f115,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f50,f112])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f51,f107])).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f97])).

fof(f53,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f54,f92])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f55,f87])).

fof(f55,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:39:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (5612)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (5636)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (5628)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (5620)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (5632)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (5611)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (5624)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (5619)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (5619)Refutation not found, incomplete strategy% (5619)------------------------------
% 0.21/0.57  % (5619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5616)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (5613)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (5635)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (5609)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.58  % (5619)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (5619)Memory used [KB]: 11001
% 0.21/0.58  % (5619)Time elapsed: 0.138 s
% 0.21/0.58  % (5619)------------------------------
% 0.21/0.58  % (5619)------------------------------
% 0.21/0.59  % (5615)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.59  % (5614)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.70/0.59  % (5633)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.70/0.61  % (5629)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.70/0.61  % (5631)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.01/0.61  % (5618)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.01/0.61  % (5625)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 2.01/0.61  % (5637)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.01/0.62  % (5617)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.01/0.62  % (5638)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 2.01/0.62  % (5610)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 2.01/0.63  % (5623)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 2.01/0.63  % (5630)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.01/0.63  % (5625)Refutation not found, incomplete strategy% (5625)------------------------------
% 2.01/0.63  % (5625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (5634)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.01/0.64  % (5621)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.01/0.64  % (5625)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.64  
% 2.01/0.64  % (5625)Memory used [KB]: 10746
% 2.01/0.64  % (5625)Time elapsed: 0.205 s
% 2.01/0.64  % (5625)------------------------------
% 2.01/0.64  % (5625)------------------------------
% 2.01/0.64  % (5622)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.01/0.64  % (5637)Refutation not found, incomplete strategy% (5637)------------------------------
% 2.01/0.64  % (5637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.65  % (5637)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.65  
% 2.01/0.65  % (5637)Memory used [KB]: 11001
% 2.01/0.65  % (5637)Time elapsed: 0.206 s
% 2.01/0.65  % (5637)------------------------------
% 2.01/0.65  % (5637)------------------------------
% 2.25/0.66  % (5626)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.25/0.67  % (5627)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.25/0.69  % (5630)Refutation found. Thanks to Tanya!
% 2.25/0.69  % SZS status Theorem for theBenchmark
% 2.25/0.69  % SZS output start Proof for theBenchmark
% 2.25/0.69  fof(f630,plain,(
% 2.25/0.69    $false),
% 2.25/0.69    inference(avatar_sat_refutation,[],[f90,f95,f100,f105,f110,f115,f120,f125,f130,f135,f140,f145,f151,f160,f165,f188,f211,f218,f228,f246,f261,f361,f395,f399,f416,f448,f476,f495,f550,f565,f611,f629])).
% 2.25/0.69  fof(f629,plain,(
% 2.25/0.69    spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_26 | ~spl4_37 | ~spl4_53),
% 2.25/0.69    inference(avatar_contradiction_clause,[],[f628])).
% 2.25/0.69  fof(f628,plain,(
% 2.25/0.69    $false | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_26 | ~spl4_37 | ~spl4_53)),
% 2.25/0.69    inference(subsumption_resolution,[],[f627,f258])).
% 2.25/0.69  fof(f258,plain,(
% 2.25/0.69    sK0 = k1_relat_1(sK2) | ~spl4_26),
% 2.25/0.69    inference(avatar_component_clause,[],[f256])).
% 2.25/0.69  fof(f256,plain,(
% 2.25/0.69    spl4_26 <=> sK0 = k1_relat_1(sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.25/0.69  fof(f627,plain,(
% 2.25/0.69    sK0 != k1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_53)),
% 2.25/0.69    inference(forward_demodulation,[],[f626,f372])).
% 2.25/0.69  fof(f372,plain,(
% 2.25/0.69    sK0 = k2_relat_1(sK3) | ~spl4_37),
% 2.25/0.69    inference(avatar_component_clause,[],[f370])).
% 2.25/0.69  fof(f370,plain,(
% 2.25/0.69    spl4_37 <=> sK0 = k2_relat_1(sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 2.25/0.69  fof(f626,plain,(
% 2.25/0.69    k1_relat_1(sK2) != k2_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_53)),
% 2.25/0.69    inference(trivial_inequality_removal,[],[f625])).
% 2.25/0.69  fof(f625,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_53)),
% 2.25/0.69    inference(forward_demodulation,[],[f624,f185])).
% 2.25/0.69  fof(f185,plain,(
% 2.25/0.69    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 2.25/0.69    inference(avatar_component_clause,[],[f183])).
% 2.25/0.69  fof(f183,plain,(
% 2.25/0.69    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.25/0.69  fof(f624,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_53)),
% 2.25/0.69    inference(subsumption_resolution,[],[f623,f164])).
% 2.25/0.69  fof(f164,plain,(
% 2.25/0.69    v1_relat_1(sK2) | ~spl4_15),
% 2.25/0.69    inference(avatar_component_clause,[],[f162])).
% 2.25/0.69  fof(f162,plain,(
% 2.25/0.69    spl4_15 <=> v1_relat_1(sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.25/0.69  fof(f623,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_53)),
% 2.25/0.69    inference(subsumption_resolution,[],[f622,f144])).
% 2.25/0.69  fof(f144,plain,(
% 2.25/0.69    v1_funct_1(sK2) | ~spl4_12),
% 2.25/0.69    inference(avatar_component_clause,[],[f142])).
% 2.25/0.69  fof(f142,plain,(
% 2.25/0.69    spl4_12 <=> v1_funct_1(sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.25/0.69  fof(f622,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_14 | ~spl4_53)),
% 2.25/0.69    inference(subsumption_resolution,[],[f621,f159])).
% 2.25/0.69  fof(f159,plain,(
% 2.25/0.69    v1_relat_1(sK3) | ~spl4_14),
% 2.25/0.69    inference(avatar_component_clause,[],[f157])).
% 2.25/0.69  fof(f157,plain,(
% 2.25/0.69    spl4_14 <=> v1_relat_1(sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.25/0.69  fof(f621,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_9 | ~spl4_53)),
% 2.25/0.69    inference(subsumption_resolution,[],[f620,f129])).
% 2.25/0.69  fof(f129,plain,(
% 2.25/0.69    v1_funct_1(sK3) | ~spl4_9),
% 2.25/0.69    inference(avatar_component_clause,[],[f127])).
% 2.25/0.69  fof(f127,plain,(
% 2.25/0.69    spl4_9 <=> v1_funct_1(sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.25/0.69  fof(f620,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_53)),
% 2.25/0.69    inference(subsumption_resolution,[],[f619,f104])).
% 2.25/0.69  fof(f104,plain,(
% 2.25/0.69    v2_funct_1(sK2) | ~spl4_4),
% 2.25/0.69    inference(avatar_component_clause,[],[f102])).
% 2.25/0.69  fof(f102,plain,(
% 2.25/0.69    spl4_4 <=> v2_funct_1(sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.25/0.69  fof(f619,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_53)),
% 2.25/0.69    inference(subsumption_resolution,[],[f614,f89])).
% 2.25/0.69  fof(f89,plain,(
% 2.25/0.69    k2_funct_1(sK2) != sK3 | spl4_1),
% 2.25/0.69    inference(avatar_component_clause,[],[f87])).
% 2.25/0.69  fof(f87,plain,(
% 2.25/0.69    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.25/0.69  fof(f614,plain,(
% 2.25/0.69    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_53),
% 2.25/0.69    inference(superposition,[],[f58,f610])).
% 2.25/0.69  fof(f610,plain,(
% 2.25/0.69    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) | ~spl4_53),
% 2.25/0.69    inference(avatar_component_clause,[],[f608])).
% 2.25/0.69  fof(f608,plain,(
% 2.25/0.69    spl4_53 <=> k6_relat_1(sK1) = k5_relat_1(sK3,sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.25/0.69  fof(f58,plain,(
% 2.25/0.69    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f23])).
% 2.25/0.69  fof(f23,plain,(
% 2.25/0.69    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.25/0.69    inference(flattening,[],[f22])).
% 2.25/0.69  fof(f22,plain,(
% 2.25/0.69    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.25/0.69    inference(ennf_transformation,[],[f3])).
% 2.25/0.69  fof(f3,axiom,(
% 2.25/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 2.25/0.69  fof(f611,plain,(
% 2.25/0.69    spl4_53 | ~spl4_39 | ~spl4_50),
% 2.25/0.69    inference(avatar_split_clause,[],[f606,f562,f390,f608])).
% 2.25/0.69  fof(f390,plain,(
% 2.25/0.69    spl4_39 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 2.25/0.69  fof(f562,plain,(
% 2.25/0.69    spl4_50 <=> sK2 = k2_funct_1(sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 2.25/0.69  fof(f606,plain,(
% 2.25/0.69    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) | (~spl4_39 | ~spl4_50)),
% 2.25/0.69    inference(forward_demodulation,[],[f392,f564])).
% 2.25/0.69  fof(f564,plain,(
% 2.25/0.69    sK2 = k2_funct_1(sK3) | ~spl4_50),
% 2.25/0.69    inference(avatar_component_clause,[],[f562])).
% 2.25/0.69  fof(f392,plain,(
% 2.25/0.69    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_39),
% 2.25/0.69    inference(avatar_component_clause,[],[f390])).
% 2.25/0.69  fof(f565,plain,(
% 2.25/0.69    ~spl4_24 | spl4_50 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_37 | ~spl4_46),
% 2.25/0.69    inference(avatar_split_clause,[],[f560,f454,f370,f223,f183,f162,f157,f142,f127,f562,f240])).
% 2.25/0.69  fof(f240,plain,(
% 2.25/0.69    spl4_24 <=> v2_funct_1(sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.25/0.69  fof(f223,plain,(
% 2.25/0.69    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.25/0.69  fof(f454,plain,(
% 2.25/0.69    spl4_46 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.25/0.69  fof(f560,plain,(
% 2.25/0.69    sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_23 | ~spl4_37 | ~spl4_46)),
% 2.25/0.69    inference(subsumption_resolution,[],[f559,f185])).
% 2.25/0.69  fof(f559,plain,(
% 2.25/0.69    sK1 != k2_relat_1(sK2) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_23 | ~spl4_37 | ~spl4_46)),
% 2.25/0.69    inference(forward_demodulation,[],[f558,f225])).
% 2.25/0.69  fof(f225,plain,(
% 2.25/0.69    sK1 = k1_relat_1(sK3) | ~spl4_23),
% 2.25/0.69    inference(avatar_component_clause,[],[f223])).
% 2.25/0.69  fof(f558,plain,(
% 2.25/0.69    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_46)),
% 2.25/0.69    inference(trivial_inequality_removal,[],[f557])).
% 2.25/0.69  fof(f557,plain,(
% 2.25/0.69    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_37 | ~spl4_46)),
% 2.25/0.69    inference(forward_demodulation,[],[f556,f372])).
% 2.25/0.69  fof(f556,plain,(
% 2.25/0.69    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_46)),
% 2.25/0.69    inference(subsumption_resolution,[],[f555,f159])).
% 2.25/0.69  fof(f555,plain,(
% 2.25/0.69    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_46)),
% 2.25/0.69    inference(subsumption_resolution,[],[f554,f129])).
% 2.25/0.69  fof(f554,plain,(
% 2.25/0.69    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_46)),
% 2.25/0.69    inference(subsumption_resolution,[],[f553,f164])).
% 2.25/0.69  fof(f553,plain,(
% 2.25/0.69    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_46)),
% 2.25/0.69    inference(subsumption_resolution,[],[f548,f144])).
% 2.25/0.69  fof(f548,plain,(
% 2.25/0.69    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_46),
% 2.25/0.69    inference(superposition,[],[f58,f456])).
% 2.25/0.69  fof(f456,plain,(
% 2.25/0.69    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_46),
% 2.25/0.69    inference(avatar_component_clause,[],[f454])).
% 2.25/0.69  fof(f550,plain,(
% 2.25/0.69    spl4_40 | ~spl4_46),
% 2.25/0.69    inference(avatar_contradiction_clause,[],[f549])).
% 2.25/0.69  fof(f549,plain,(
% 2.25/0.69    $false | (spl4_40 | ~spl4_46)),
% 2.25/0.69    inference(subsumption_resolution,[],[f545,f67])).
% 2.25/0.69  fof(f67,plain,(
% 2.25/0.69    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.25/0.69    inference(cnf_transformation,[],[f2])).
% 2.25/0.69  fof(f2,axiom,(
% 2.25/0.69    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 2.25/0.69  fof(f545,plain,(
% 2.25/0.69    ~v2_funct_1(k6_relat_1(sK0)) | (spl4_40 | ~spl4_46)),
% 2.25/0.69    inference(backward_demodulation,[],[f415,f456])).
% 2.25/0.69  fof(f415,plain,(
% 2.25/0.69    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_40),
% 2.25/0.69    inference(avatar_component_clause,[],[f413])).
% 2.25/0.69  fof(f413,plain,(
% 2.25/0.69    spl4_40 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 2.25/0.69  fof(f495,plain,(
% 2.25/0.69    spl4_46 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_44),
% 2.25/0.69    inference(avatar_split_clause,[],[f494,f445,f142,f132,f127,f117,f454])).
% 2.25/0.69  fof(f117,plain,(
% 2.25/0.69    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.25/0.69  fof(f132,plain,(
% 2.25/0.69    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.25/0.69  fof(f445,plain,(
% 2.25/0.69    spl4_44 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.25/0.69  fof(f494,plain,(
% 2.25/0.69    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_44)),
% 2.25/0.69    inference(subsumption_resolution,[],[f493,f144])).
% 2.25/0.69  fof(f493,plain,(
% 2.25/0.69    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_44)),
% 2.25/0.69    inference(subsumption_resolution,[],[f492,f134])).
% 2.25/0.69  fof(f134,plain,(
% 2.25/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 2.25/0.69    inference(avatar_component_clause,[],[f132])).
% 2.25/0.69  fof(f492,plain,(
% 2.25/0.69    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_44)),
% 2.25/0.69    inference(subsumption_resolution,[],[f491,f129])).
% 2.25/0.69  fof(f491,plain,(
% 2.25/0.69    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_44)),
% 2.25/0.69    inference(subsumption_resolution,[],[f483,f119])).
% 2.25/0.69  fof(f119,plain,(
% 2.25/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 2.25/0.69    inference(avatar_component_clause,[],[f117])).
% 2.25/0.69  fof(f483,plain,(
% 2.25/0.69    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_44),
% 2.25/0.69    inference(superposition,[],[f75,f447])).
% 2.25/0.69  fof(f447,plain,(
% 2.25/0.69    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_44),
% 2.25/0.69    inference(avatar_component_clause,[],[f445])).
% 2.25/0.69  fof(f75,plain,(
% 2.25/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f35])).
% 2.25/0.69  fof(f35,plain,(
% 2.25/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.25/0.69    inference(flattening,[],[f34])).
% 2.25/0.69  fof(f34,plain,(
% 2.25/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.25/0.69    inference(ennf_transformation,[],[f11])).
% 2.25/0.69  fof(f11,axiom,(
% 2.25/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.25/0.69  fof(f476,plain,(
% 2.25/0.69    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_43),
% 2.25/0.69    inference(avatar_contradiction_clause,[],[f475])).
% 2.25/0.69  fof(f475,plain,(
% 2.25/0.69    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_43)),
% 2.25/0.69    inference(subsumption_resolution,[],[f474,f144])).
% 2.25/0.69  fof(f474,plain,(
% 2.25/0.69    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_43)),
% 2.25/0.69    inference(subsumption_resolution,[],[f473,f134])).
% 2.25/0.69  fof(f473,plain,(
% 2.25/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_43)),
% 2.25/0.69    inference(subsumption_resolution,[],[f472,f129])).
% 2.25/0.69  fof(f472,plain,(
% 2.25/0.69    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_43)),
% 2.25/0.69    inference(subsumption_resolution,[],[f469,f119])).
% 2.25/0.69  fof(f469,plain,(
% 2.25/0.69    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_43),
% 2.25/0.69    inference(resolution,[],[f443,f74])).
% 2.25/0.69  fof(f74,plain,(
% 2.25/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f33])).
% 2.25/0.69  fof(f33,plain,(
% 2.25/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.25/0.69    inference(flattening,[],[f32])).
% 2.25/0.69  fof(f32,plain,(
% 2.25/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.25/0.69    inference(ennf_transformation,[],[f9])).
% 2.25/0.69  fof(f9,axiom,(
% 2.25/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.25/0.69  fof(f443,plain,(
% 2.25/0.69    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_43),
% 2.25/0.69    inference(avatar_component_clause,[],[f441])).
% 2.25/0.69  fof(f441,plain,(
% 2.25/0.69    spl4_43 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 2.25/0.69  fof(f448,plain,(
% 2.25/0.69    ~spl4_43 | spl4_44 | ~spl4_13),
% 2.25/0.69    inference(avatar_split_clause,[],[f437,f148,f445,f441])).
% 2.25/0.69  fof(f148,plain,(
% 2.25/0.69    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.25/0.69  fof(f437,plain,(
% 2.25/0.69    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 2.25/0.69    inference(resolution,[],[f249,f150])).
% 2.25/0.69  fof(f150,plain,(
% 2.25/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 2.25/0.69    inference(avatar_component_clause,[],[f148])).
% 2.25/0.69  fof(f249,plain,(
% 2.25/0.69    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.25/0.69    inference(resolution,[],[f68,f152])).
% 2.25/0.69  fof(f152,plain,(
% 2.25/0.69    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.25/0.69    inference(forward_demodulation,[],[f71,f72])).
% 2.25/0.69  fof(f72,plain,(
% 2.25/0.69    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f12])).
% 2.25/0.69  fof(f12,axiom,(
% 2.25/0.69    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.25/0.69  fof(f71,plain,(
% 2.25/0.69    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.25/0.69    inference(cnf_transformation,[],[f17])).
% 2.25/0.69  fof(f17,plain,(
% 2.25/0.69    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.25/0.69    inference(pure_predicate_removal,[],[f10])).
% 2.25/0.69  fof(f10,axiom,(
% 2.25/0.69    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.25/0.69  fof(f68,plain,(
% 2.25/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.69    inference(cnf_transformation,[],[f43])).
% 2.25/0.69  fof(f43,plain,(
% 2.25/0.69    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(nnf_transformation,[],[f29])).
% 2.25/0.69  fof(f29,plain,(
% 2.25/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(flattening,[],[f28])).
% 2.25/0.69  fof(f28,plain,(
% 2.25/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.25/0.69    inference(ennf_transformation,[],[f7])).
% 2.25/0.69  fof(f7,axiom,(
% 2.25/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.25/0.69  fof(f416,plain,(
% 2.25/0.69    ~spl4_40 | ~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_25),
% 2.25/0.69    inference(avatar_split_clause,[],[f411,f244,f183,f162,f142,f413])).
% 2.25/0.69  fof(f244,plain,(
% 2.25/0.69    spl4_25 <=> ! [X0] : (k2_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK3)))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.25/0.69  fof(f411,plain,(
% 2.25/0.69    ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_25)),
% 2.25/0.69    inference(subsumption_resolution,[],[f410,f144])).
% 2.25/0.69  fof(f410,plain,(
% 2.25/0.69    ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_15 | ~spl4_18 | ~spl4_25)),
% 2.25/0.69    inference(subsumption_resolution,[],[f409,f164])).
% 2.25/0.69  fof(f409,plain,(
% 2.25/0.69    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_18 | ~spl4_25)),
% 2.25/0.69    inference(trivial_inequality_removal,[],[f407])).
% 2.25/0.69  fof(f407,plain,(
% 2.25/0.69    sK1 != sK1 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_18 | ~spl4_25)),
% 2.25/0.69    inference(superposition,[],[f245,f185])).
% 2.25/0.69  fof(f245,plain,(
% 2.25/0.69    ( ! [X0] : (k2_relat_1(X0) != sK1 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK3))) ) | ~spl4_25),
% 2.25/0.69    inference(avatar_component_clause,[],[f244])).
% 2.25/0.69  fof(f399,plain,(
% 2.25/0.69    spl4_39 | ~spl4_24 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36),
% 2.25/0.69    inference(avatar_split_clause,[],[f398,f358,f127,f122,f117,f97,f240,f390])).
% 2.25/0.69  fof(f97,plain,(
% 2.25/0.69    spl4_3 <=> k1_xboole_0 = sK0),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.25/0.69  fof(f122,plain,(
% 2.25/0.69    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.25/0.69  fof(f358,plain,(
% 2.25/0.69    spl4_36 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.25/0.69  fof(f398,plain,(
% 2.25/0.69    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36)),
% 2.25/0.69    inference(subsumption_resolution,[],[f397,f129])).
% 2.25/0.69  fof(f397,plain,(
% 2.25/0.69    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_36)),
% 2.25/0.69    inference(subsumption_resolution,[],[f396,f124])).
% 2.25/0.69  fof(f124,plain,(
% 2.25/0.69    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 2.25/0.69    inference(avatar_component_clause,[],[f122])).
% 2.25/0.69  fof(f396,plain,(
% 2.25/0.69    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_36)),
% 2.25/0.69    inference(subsumption_resolution,[],[f384,f119])).
% 2.25/0.69  fof(f384,plain,(
% 2.25/0.69    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_36)),
% 2.25/0.69    inference(subsumption_resolution,[],[f366,f99])).
% 2.25/0.69  fof(f99,plain,(
% 2.25/0.69    k1_xboole_0 != sK0 | spl4_3),
% 2.25/0.69    inference(avatar_component_clause,[],[f97])).
% 2.25/0.69  fof(f366,plain,(
% 2.25/0.69    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 2.25/0.69    inference(trivial_inequality_removal,[],[f364])).
% 2.25/0.69  fof(f364,plain,(
% 2.25/0.69    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_36),
% 2.25/0.69    inference(superposition,[],[f286,f360])).
% 2.25/0.69  fof(f360,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_36),
% 2.25/0.69    inference(avatar_component_clause,[],[f358])).
% 2.25/0.69  fof(f286,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.25/0.69    inference(forward_demodulation,[],[f56,f72])).
% 2.25/0.69  fof(f56,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f21])).
% 2.25/0.69  fof(f21,plain,(
% 2.25/0.69    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.25/0.69    inference(flattening,[],[f20])).
% 2.25/0.69  fof(f20,plain,(
% 2.25/0.69    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.25/0.69    inference(ennf_transformation,[],[f14])).
% 2.25/0.69  fof(f14,axiom,(
% 2.25/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.25/0.69  fof(f395,plain,(
% 2.25/0.69    spl4_37 | ~spl4_7 | ~spl4_36),
% 2.25/0.69    inference(avatar_split_clause,[],[f394,f358,f117,f370])).
% 2.25/0.69  fof(f394,plain,(
% 2.25/0.69    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_36)),
% 2.25/0.69    inference(subsumption_resolution,[],[f365,f119])).
% 2.25/0.69  fof(f365,plain,(
% 2.25/0.69    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_36),
% 2.25/0.69    inference(superposition,[],[f76,f360])).
% 2.25/0.69  fof(f76,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.69    inference(cnf_transformation,[],[f36])).
% 2.25/0.69  fof(f36,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(ennf_transformation,[],[f6])).
% 2.25/0.69  fof(f6,axiom,(
% 2.25/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.25/0.69  fof(f361,plain,(
% 2.25/0.69    spl4_36 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 2.25/0.69    inference(avatar_split_clause,[],[f356,f148,f142,f137,f132,f127,f122,f117,f358])).
% 2.25/0.69  fof(f137,plain,(
% 2.25/0.69    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.25/0.69  fof(f356,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.25/0.69    inference(subsumption_resolution,[],[f355,f129])).
% 2.25/0.69  fof(f355,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.25/0.69    inference(subsumption_resolution,[],[f354,f124])).
% 2.25/0.69  fof(f354,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.25/0.69    inference(subsumption_resolution,[],[f353,f119])).
% 2.25/0.69  fof(f353,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 2.25/0.69    inference(subsumption_resolution,[],[f352,f144])).
% 2.25/0.69  fof(f352,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 2.25/0.69    inference(subsumption_resolution,[],[f351,f139])).
% 2.25/0.69  fof(f139,plain,(
% 2.25/0.69    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 2.25/0.69    inference(avatar_component_clause,[],[f137])).
% 2.25/0.69  fof(f351,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 2.25/0.69    inference(subsumption_resolution,[],[f348,f134])).
% 2.25/0.69  fof(f348,plain,(
% 2.25/0.69    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 2.25/0.69    inference(resolution,[],[f347,f150])).
% 2.25/0.69  fof(f347,plain,(
% 2.25/0.69    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.25/0.69    inference(forward_demodulation,[],[f70,f72])).
% 2.25/0.69  fof(f70,plain,(
% 2.25/0.69    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f31])).
% 2.25/0.69  fof(f31,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.25/0.69    inference(flattening,[],[f30])).
% 2.25/0.69  fof(f30,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.25/0.69    inference(ennf_transformation,[],[f13])).
% 2.25/0.69  fof(f13,axiom,(
% 2.25/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.25/0.69  fof(f261,plain,(
% 2.25/0.69    spl4_26 | ~spl4_10 | ~spl4_22),
% 2.25/0.69    inference(avatar_split_clause,[],[f260,f215,f132,f256])).
% 2.25/0.69  fof(f215,plain,(
% 2.25/0.69    spl4_22 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.25/0.69  fof(f260,plain,(
% 2.25/0.69    sK0 = k1_relat_1(sK2) | (~spl4_10 | ~spl4_22)),
% 2.25/0.69    inference(subsumption_resolution,[],[f252,f134])).
% 2.25/0.69  fof(f252,plain,(
% 2.25/0.69    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_22),
% 2.25/0.69    inference(superposition,[],[f78,f217])).
% 2.25/0.69  fof(f217,plain,(
% 2.25/0.69    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_22),
% 2.25/0.69    inference(avatar_component_clause,[],[f215])).
% 2.25/0.69  fof(f78,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.69    inference(cnf_transformation,[],[f38])).
% 2.25/0.69  fof(f38,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(ennf_transformation,[],[f5])).
% 2.25/0.69  fof(f5,axiom,(
% 2.25/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.25/0.69  fof(f246,plain,(
% 2.25/0.69    spl4_24 | spl4_25 | ~spl4_9 | ~spl4_14 | ~spl4_23),
% 2.25/0.69    inference(avatar_split_clause,[],[f238,f223,f157,f127,f244,f240])).
% 2.25/0.69  fof(f238,plain,(
% 2.25/0.69    ( ! [X0] : (k2_relat_1(X0) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X0,sK3)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_9 | ~spl4_14 | ~spl4_23)),
% 2.25/0.69    inference(subsumption_resolution,[],[f237,f159])).
% 2.25/0.69  fof(f237,plain,(
% 2.25/0.69    ( ! [X0] : (k2_relat_1(X0) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X0,sK3)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) ) | (~spl4_9 | ~spl4_23)),
% 2.25/0.69    inference(subsumption_resolution,[],[f236,f129])).
% 2.25/0.69  fof(f236,plain,(
% 2.25/0.69    ( ! [X0] : (k2_relat_1(X0) != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(X0,sK3)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl4_23),
% 2.25/0.69    inference(superposition,[],[f66,f225])).
% 2.25/0.69  fof(f66,plain,(
% 2.25/0.69    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f27])).
% 2.25/0.69  fof(f27,plain,(
% 2.25/0.69    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.25/0.69    inference(flattening,[],[f26])).
% 2.25/0.69  fof(f26,plain,(
% 2.25/0.69    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.25/0.69    inference(ennf_transformation,[],[f1])).
% 2.25/0.69  fof(f1,axiom,(
% 2.25/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 2.25/0.69  fof(f228,plain,(
% 2.25/0.69    spl4_23 | ~spl4_7 | ~spl4_21),
% 2.25/0.69    inference(avatar_split_clause,[],[f227,f208,f117,f223])).
% 2.25/0.69  fof(f208,plain,(
% 2.25/0.69    spl4_21 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.25/0.69  fof(f227,plain,(
% 2.25/0.69    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_21)),
% 2.25/0.69    inference(subsumption_resolution,[],[f220,f119])).
% 2.25/0.69  fof(f220,plain,(
% 2.25/0.69    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_21),
% 2.25/0.69    inference(superposition,[],[f78,f210])).
% 2.25/0.69  fof(f210,plain,(
% 2.25/0.69    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_21),
% 2.25/0.69    inference(avatar_component_clause,[],[f208])).
% 2.25/0.69  fof(f218,plain,(
% 2.25/0.69    spl4_22 | spl4_2 | ~spl4_10 | ~spl4_11),
% 2.25/0.69    inference(avatar_split_clause,[],[f213,f137,f132,f92,f215])).
% 2.25/0.69  fof(f92,plain,(
% 2.25/0.69    spl4_2 <=> k1_xboole_0 = sK1),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.25/0.69  fof(f213,plain,(
% 2.25/0.69    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_2 | ~spl4_10 | ~spl4_11)),
% 2.25/0.69    inference(subsumption_resolution,[],[f212,f94])).
% 2.25/0.69  fof(f94,plain,(
% 2.25/0.69    k1_xboole_0 != sK1 | spl4_2),
% 2.25/0.69    inference(avatar_component_clause,[],[f92])).
% 2.25/0.69  fof(f212,plain,(
% 2.25/0.69    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl4_10 | ~spl4_11)),
% 2.25/0.69    inference(subsumption_resolution,[],[f203,f139])).
% 2.25/0.69  fof(f203,plain,(
% 2.25/0.69    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_10),
% 2.25/0.69    inference(resolution,[],[f59,f134])).
% 2.25/0.69  fof(f59,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 2.25/0.69    inference(cnf_transformation,[],[f42])).
% 2.25/0.69  fof(f42,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(nnf_transformation,[],[f25])).
% 2.25/0.69  fof(f25,plain,(
% 2.25/0.69    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(flattening,[],[f24])).
% 2.25/0.69  fof(f24,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(ennf_transformation,[],[f8])).
% 2.25/0.69  fof(f8,axiom,(
% 2.25/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.25/0.69  fof(f211,plain,(
% 2.25/0.69    spl4_21 | spl4_3 | ~spl4_7 | ~spl4_8),
% 2.25/0.69    inference(avatar_split_clause,[],[f206,f122,f117,f97,f208])).
% 2.25/0.69  fof(f206,plain,(
% 2.25/0.69    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 2.25/0.69    inference(subsumption_resolution,[],[f205,f99])).
% 2.25/0.69  fof(f205,plain,(
% 2.25/0.69    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 2.25/0.69    inference(subsumption_resolution,[],[f202,f124])).
% 2.25/0.69  fof(f202,plain,(
% 2.25/0.69    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 2.25/0.69    inference(resolution,[],[f59,f119])).
% 2.25/0.69  fof(f188,plain,(
% 2.25/0.69    spl4_18 | ~spl4_6 | ~spl4_10),
% 2.25/0.69    inference(avatar_split_clause,[],[f187,f132,f112,f183])).
% 2.25/0.69  fof(f112,plain,(
% 2.25/0.69    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.25/0.69  fof(f187,plain,(
% 2.25/0.69    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 2.25/0.69    inference(subsumption_resolution,[],[f180,f134])).
% 2.25/0.69  fof(f180,plain,(
% 2.25/0.69    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 2.25/0.69    inference(superposition,[],[f114,f76])).
% 2.25/0.69  fof(f114,plain,(
% 2.25/0.69    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 2.25/0.69    inference(avatar_component_clause,[],[f112])).
% 2.25/0.69  fof(f165,plain,(
% 2.25/0.69    spl4_15 | ~spl4_10),
% 2.25/0.69    inference(avatar_split_clause,[],[f154,f132,f162])).
% 2.25/0.69  fof(f154,plain,(
% 2.25/0.69    v1_relat_1(sK2) | ~spl4_10),
% 2.25/0.69    inference(resolution,[],[f77,f134])).
% 2.25/0.69  fof(f77,plain,(
% 2.25/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.25/0.69    inference(cnf_transformation,[],[f37])).
% 2.25/0.69  fof(f37,plain,(
% 2.25/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.69    inference(ennf_transformation,[],[f4])).
% 2.25/0.69  fof(f4,axiom,(
% 2.25/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.25/0.69  fof(f160,plain,(
% 2.25/0.69    spl4_14 | ~spl4_7),
% 2.25/0.69    inference(avatar_split_clause,[],[f153,f117,f157])).
% 2.25/0.69  fof(f153,plain,(
% 2.25/0.69    v1_relat_1(sK3) | ~spl4_7),
% 2.25/0.69    inference(resolution,[],[f77,f119])).
% 2.25/0.69  fof(f151,plain,(
% 2.25/0.69    spl4_13 | ~spl4_5),
% 2.25/0.69    inference(avatar_split_clause,[],[f146,f107,f148])).
% 2.25/0.69  fof(f107,plain,(
% 2.25/0.69    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.25/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.25/0.69  fof(f146,plain,(
% 2.25/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 2.25/0.69    inference(backward_demodulation,[],[f109,f72])).
% 2.25/0.69  fof(f109,plain,(
% 2.25/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 2.25/0.69    inference(avatar_component_clause,[],[f107])).
% 2.25/0.69  fof(f145,plain,(
% 2.25/0.69    spl4_12),
% 2.25/0.69    inference(avatar_split_clause,[],[f44,f142])).
% 2.25/0.69  fof(f44,plain,(
% 2.25/0.69    v1_funct_1(sK2)),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f41,plain,(
% 2.25/0.69    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.25/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f40,f39])).
% 2.25/0.69  fof(f39,plain,(
% 2.25/0.69    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.25/0.69    introduced(choice_axiom,[])).
% 2.25/0.69  fof(f40,plain,(
% 2.25/0.69    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.25/0.69    introduced(choice_axiom,[])).
% 2.25/0.69  fof(f19,plain,(
% 2.25/0.69    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.25/0.69    inference(flattening,[],[f18])).
% 2.25/0.69  fof(f18,plain,(
% 2.25/0.69    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.25/0.69    inference(ennf_transformation,[],[f16])).
% 2.25/0.69  fof(f16,negated_conjecture,(
% 2.25/0.69    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.25/0.69    inference(negated_conjecture,[],[f15])).
% 2.25/0.69  fof(f15,conjecture,(
% 2.25/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.25/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.25/0.69  fof(f140,plain,(
% 2.25/0.69    spl4_11),
% 2.25/0.69    inference(avatar_split_clause,[],[f45,f137])).
% 2.25/0.69  fof(f45,plain,(
% 2.25/0.69    v1_funct_2(sK2,sK0,sK1)),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f135,plain,(
% 2.25/0.69    spl4_10),
% 2.25/0.69    inference(avatar_split_clause,[],[f46,f132])).
% 2.25/0.69  fof(f46,plain,(
% 2.25/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f130,plain,(
% 2.25/0.69    spl4_9),
% 2.25/0.69    inference(avatar_split_clause,[],[f47,f127])).
% 2.25/0.69  fof(f47,plain,(
% 2.25/0.69    v1_funct_1(sK3)),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f125,plain,(
% 2.25/0.69    spl4_8),
% 2.25/0.69    inference(avatar_split_clause,[],[f48,f122])).
% 2.25/0.69  fof(f48,plain,(
% 2.25/0.69    v1_funct_2(sK3,sK1,sK0)),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f120,plain,(
% 2.25/0.69    spl4_7),
% 2.25/0.69    inference(avatar_split_clause,[],[f49,f117])).
% 2.25/0.69  fof(f49,plain,(
% 2.25/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f115,plain,(
% 2.25/0.69    spl4_6),
% 2.25/0.69    inference(avatar_split_clause,[],[f50,f112])).
% 2.25/0.69  fof(f50,plain,(
% 2.25/0.69    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f110,plain,(
% 2.25/0.69    spl4_5),
% 2.25/0.69    inference(avatar_split_clause,[],[f51,f107])).
% 2.25/0.69  fof(f51,plain,(
% 2.25/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f105,plain,(
% 2.25/0.69    spl4_4),
% 2.25/0.69    inference(avatar_split_clause,[],[f52,f102])).
% 2.25/0.69  fof(f52,plain,(
% 2.25/0.69    v2_funct_1(sK2)),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f100,plain,(
% 2.25/0.69    ~spl4_3),
% 2.25/0.69    inference(avatar_split_clause,[],[f53,f97])).
% 2.25/0.69  fof(f53,plain,(
% 2.25/0.69    k1_xboole_0 != sK0),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f95,plain,(
% 2.25/0.69    ~spl4_2),
% 2.25/0.69    inference(avatar_split_clause,[],[f54,f92])).
% 2.25/0.69  fof(f54,plain,(
% 2.25/0.69    k1_xboole_0 != sK1),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  fof(f90,plain,(
% 2.25/0.69    ~spl4_1),
% 2.25/0.69    inference(avatar_split_clause,[],[f55,f87])).
% 2.25/0.69  fof(f55,plain,(
% 2.25/0.69    k2_funct_1(sK2) != sK3),
% 2.25/0.69    inference(cnf_transformation,[],[f41])).
% 2.25/0.69  % SZS output end Proof for theBenchmark
% 2.25/0.69  % (5630)------------------------------
% 2.25/0.69  % (5630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.69  % (5630)Termination reason: Refutation
% 2.25/0.69  
% 2.25/0.69  % (5630)Memory used [KB]: 6652
% 2.25/0.69  % (5630)Time elapsed: 0.271 s
% 2.25/0.69  % (5630)------------------------------
% 2.25/0.69  % (5630)------------------------------
% 2.25/0.69  % (5608)Success in time 0.332 s
%------------------------------------------------------------------------------
