%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:51 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  260 ( 512 expanded)
%              Number of leaves         :   53 ( 214 expanded)
%              Depth                    :   13
%              Number of atoms          : 1123 (2598 expanded)
%              Number of equality atoms :  235 ( 674 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f930,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f178,f188,f194,f202,f218,f269,f290,f408,f436,f462,f526,f548,f585,f632,f737,f756,f808,f872,f929])).

fof(f929,plain,
    ( ~ spl4_14
    | spl4_18
    | ~ spl4_57 ),
    inference(avatar_contradiction_clause,[],[f928])).

fof(f928,plain,
    ( $false
    | ~ spl4_14
    | spl4_18
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f927,f187])).

fof(f187,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f927,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_18
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f914,f217])).

fof(f217,plain,
    ( sK3 != k4_relat_1(sK2)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl4_18
  <=> sK3 = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f914,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_57 ),
    inference(superposition,[],[f103,f828])).

fof(f828,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f826])).

fof(f826,plain,
    ( spl4_57
  <=> sK2 = k4_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f103,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f872,plain,
    ( spl4_57
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_43
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f871,f749,f523,f185,f154,f826])).

fof(f154,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f523,plain,
    ( spl4_43
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f749,plain,
    ( spl4_55
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f871,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_43
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f870,f187])).

fof(f870,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_43
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f869,f156])).

fof(f156,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f869,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f821,f525])).

fof(f525,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f523])).

fof(f821,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_55 ),
    inference(superposition,[],[f76,f751])).

fof(f751,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f749])).

fof(f76,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f808,plain,
    ( ~ spl4_14
    | ~ spl4_16
    | ~ spl4_38
    | spl4_56 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_38
    | spl4_56 ),
    inference(subsumption_resolution,[],[f806,f201])).

fof(f201,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_16
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f806,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ spl4_14
    | ~ spl4_38
    | spl4_56 ),
    inference(subsumption_resolution,[],[f805,f435])).

fof(f435,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl4_38
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f805,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl4_14
    | spl4_56 ),
    inference(equality_resolution,[],[f761])).

fof(f761,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(sK0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) )
    | ~ spl4_14
    | spl4_56 ),
    inference(subsumption_resolution,[],[f760,f187])).

fof(f760,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(sK0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl4_56 ),
    inference(superposition,[],[f755,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f755,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | spl4_56 ),
    inference(avatar_component_clause,[],[f753])).

fof(f753,plain,
    ( spl4_56
  <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f756,plain,
    ( spl4_55
    | ~ spl4_56
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_40
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f746,f554,f523,f454,f285,f191,f185,f169,f154,f753,f749])).

fof(f169,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f191,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f285,plain,
    ( spl4_25
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f454,plain,
    ( spl4_40
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f554,plain,
    ( spl4_47
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f746,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_40
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f745,f456])).

fof(f456,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f454])).

fof(f745,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f744,f287])).

fof(f287,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f285])).

fof(f744,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f743,f187])).

fof(f743,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f742,f156])).

fof(f742,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f741,f193])).

fof(f193,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f741,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f740,f171])).

fof(f171,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f740,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_43
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f735,f525])).

fof(f735,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_47 ),
    inference(superposition,[],[f73,f556])).

fof(f556,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f554])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f737,plain,
    ( spl4_42
    | ~ spl4_47 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | spl4_42
    | ~ spl4_47 ),
    inference(subsumption_resolution,[],[f732,f88])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f732,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | spl4_42
    | ~ spl4_47 ),
    inference(backward_demodulation,[],[f521,f556])).

fof(f521,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f519])).

fof(f519,plain,
    ( spl4_42
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f632,plain,
    ( spl4_47
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f631,f545,f169,f159,f154,f144,f554])).

fof(f144,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f159,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f545,plain,
    ( spl4_45
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f631,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f630,f171])).

fof(f630,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f629,f161])).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f629,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f628,f156])).

fof(f628,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f619,f146])).

fof(f146,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f619,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_45 ),
    inference(superposition,[],[f95,f547])).

fof(f547,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f545])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f585,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_44 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_44 ),
    inference(subsumption_resolution,[],[f583,f171])).

fof(f583,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_44 ),
    inference(subsumption_resolution,[],[f582,f161])).

fof(f582,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_44 ),
    inference(subsumption_resolution,[],[f581,f156])).

fof(f581,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_44 ),
    inference(subsumption_resolution,[],[f578,f146])).

fof(f578,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_44 ),
    inference(resolution,[],[f543,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f543,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl4_44
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f548,plain,
    ( ~ spl4_44
    | spl4_45
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f537,f175,f545,f541])).

fof(f175,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f537,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f307,f177])).

fof(f177,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f307,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f89,f179])).

fof(f179,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f91,f92])).

fof(f92,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f526,plain,
    ( ~ spl4_42
    | spl4_43
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f517,f454,f285,f191,f185,f169,f154,f523,f519])).

fof(f517,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f516,f187])).

fof(f516,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f515,f156])).

fof(f515,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(trivial_inequality_removal,[],[f514])).

fof(f514,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_40 ),
    inference(superposition,[],[f470,f287])).

fof(f470,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | v2_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f469,f193])).

fof(f469,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | v2_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_12
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f464,f171])).

fof(f464,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK1
        | v2_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_40 ),
    inference(superposition,[],[f86,f456])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f462,plain,
    ( spl4_40
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f461,f405,f191,f169,f129,f454])).

fof(f129,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f405,plain,
    ( spl4_36
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f461,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f460,f96])).

fof(f96,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f460,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f459,f193])).

fof(f459,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f458,f171])).

fof(f458,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f439,f131])).

fof(f131,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f439,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_36 ),
    inference(superposition,[],[f74,f407])).

fof(f407,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f405])).

fof(f74,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f436,plain,
    ( spl4_38
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f431,f175,f169,f164,f159,f154,f149,f144,f433])).

fof(f149,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f164,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f431,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f430,f171])).

fof(f430,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f429,f166])).

fof(f166,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f429,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f428,f161])).

fof(f428,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f427,f156])).

fof(f427,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f426,f151])).

fof(f151,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f426,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f423,f146])).

fof(f423,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(resolution,[],[f422,f177])).

fof(f422,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | v2_funct_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f84,f92])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f408,plain,
    ( spl4_36
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f403,f169,f164,f159,f139,f129,f119,f405])).

fof(f119,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f139,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f403,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f402,f171])).

fof(f402,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f401,f166])).

fof(f401,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f400,f161])).

fof(f400,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f399,f131])).

fof(f399,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f398,f121])).

fof(f121,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f398,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f345,f141])).

fof(f141,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f345,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f72,f92])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f290,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f289,f266,f144,f285])).

fof(f266,plain,
    ( spl4_23
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f289,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f281,f146])).

fof(f281,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_23 ),
    inference(superposition,[],[f100,f268])).

fof(f268,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f266])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f269,plain,
    ( spl4_23
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f264,f149,f144,f124,f266])).

fof(f124,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f264,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f263,f126])).

fof(f126,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f263,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f260,f151])).

fof(f260,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f77,f146])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f218,plain,
    ( ~ spl4_18
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f213,f191,f169,f129,f114,f215])).

fof(f114,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f213,plain,
    ( sK3 != k4_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f212,f193])).

fof(f212,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f211,f171])).

fof(f211,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f210,f131])).

fof(f210,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(superposition,[],[f116,f76])).

fof(f116,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f202,plain,
    ( spl4_16
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f195,f144,f199])).

fof(f195,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f104,f146])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f194,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f189,f159,f191])).

fof(f189,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f181,f99])).

fof(f99,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f181,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f98,f161])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f188,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f183,f144,f185])).

fof(f183,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f180,f99])).

fof(f180,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f98,f146])).

fof(f178,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f173,f134,f175])).

fof(f134,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f173,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f136,f92])).

fof(f136,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f172,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f59,f169])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f54,f53])).

fof(f53,plain,
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

fof(f54,plain,
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f167,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f60,f164])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f162,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f61,f159])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f157,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f62,f154])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f152,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f63,f149])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f147,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f64,f144])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f142,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f65,f139])).

fof(f65,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f137,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f66,f134])).

fof(f66,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f132,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f67,f129])).

fof(f67,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f127,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f68,f124])).

fof(f68,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f55])).

fof(f122,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f69,f119])).

fof(f69,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f117,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f70,f114])).

fof(f70,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:18:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (5462)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (5454)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (5446)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (5443)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (5439)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (5453)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (5444)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (5468)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (5465)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (5440)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (5441)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (5457)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (5450)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (5442)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (5447)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (5464)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (5445)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (5466)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (5467)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (5460)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (5458)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (5456)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (5459)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (5461)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (5448)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (5451)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (5449)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.56  % (5455)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.56  % (5452)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (5455)Refutation not found, incomplete strategy% (5455)------------------------------
% 1.50/0.56  % (5455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (5455)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (5455)Memory used [KB]: 10746
% 1.50/0.56  % (5455)Time elapsed: 0.151 s
% 1.50/0.56  % (5455)------------------------------
% 1.50/0.56  % (5455)------------------------------
% 1.50/0.57  % (5463)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.57  % (5467)Refutation not found, incomplete strategy% (5467)------------------------------
% 1.50/0.57  % (5467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (5467)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (5467)Memory used [KB]: 11001
% 1.50/0.57  % (5467)Time elapsed: 0.159 s
% 1.50/0.57  % (5467)------------------------------
% 1.50/0.57  % (5467)------------------------------
% 1.61/0.58  % (5449)Refutation not found, incomplete strategy% (5449)------------------------------
% 1.61/0.58  % (5449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (5449)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (5449)Memory used [KB]: 11001
% 1.61/0.58  % (5449)Time elapsed: 0.148 s
% 1.61/0.58  % (5449)------------------------------
% 1.61/0.58  % (5449)------------------------------
% 1.61/0.60  % (5460)Refutation found. Thanks to Tanya!
% 1.61/0.60  % SZS status Theorem for theBenchmark
% 1.61/0.60  % SZS output start Proof for theBenchmark
% 1.61/0.60  fof(f930,plain,(
% 1.61/0.60    $false),
% 1.61/0.60    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f152,f157,f162,f167,f172,f178,f188,f194,f202,f218,f269,f290,f408,f436,f462,f526,f548,f585,f632,f737,f756,f808,f872,f929])).
% 1.61/0.60  fof(f929,plain,(
% 1.61/0.60    ~spl4_14 | spl4_18 | ~spl4_57),
% 1.61/0.60    inference(avatar_contradiction_clause,[],[f928])).
% 1.61/0.60  fof(f928,plain,(
% 1.61/0.60    $false | (~spl4_14 | spl4_18 | ~spl4_57)),
% 1.61/0.60    inference(subsumption_resolution,[],[f927,f187])).
% 1.61/0.60  fof(f187,plain,(
% 1.61/0.60    v1_relat_1(sK3) | ~spl4_14),
% 1.61/0.60    inference(avatar_component_clause,[],[f185])).
% 1.61/0.60  fof(f185,plain,(
% 1.61/0.60    spl4_14 <=> v1_relat_1(sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.61/0.60  fof(f927,plain,(
% 1.61/0.60    ~v1_relat_1(sK3) | (spl4_18 | ~spl4_57)),
% 1.61/0.60    inference(subsumption_resolution,[],[f914,f217])).
% 1.61/0.60  fof(f217,plain,(
% 1.61/0.60    sK3 != k4_relat_1(sK2) | spl4_18),
% 1.61/0.60    inference(avatar_component_clause,[],[f215])).
% 1.61/0.60  fof(f215,plain,(
% 1.61/0.60    spl4_18 <=> sK3 = k4_relat_1(sK2)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.61/0.60  fof(f914,plain,(
% 1.61/0.60    sK3 = k4_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_57),
% 1.61/0.60    inference(superposition,[],[f103,f828])).
% 1.61/0.60  fof(f828,plain,(
% 1.61/0.60    sK2 = k4_relat_1(sK3) | ~spl4_57),
% 1.61/0.60    inference(avatar_component_clause,[],[f826])).
% 1.61/0.60  fof(f826,plain,(
% 1.61/0.60    spl4_57 <=> sK2 = k4_relat_1(sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.61/0.60  fof(f103,plain,(
% 1.61/0.60    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f51])).
% 1.61/0.60  fof(f51,plain,(
% 1.61/0.60    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.61/0.60    inference(ennf_transformation,[],[f3])).
% 1.61/0.60  fof(f3,axiom,(
% 1.61/0.60    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.61/0.60  fof(f872,plain,(
% 1.61/0.60    spl4_57 | ~spl4_9 | ~spl4_14 | ~spl4_43 | ~spl4_55),
% 1.61/0.60    inference(avatar_split_clause,[],[f871,f749,f523,f185,f154,f826])).
% 1.61/0.60  fof(f154,plain,(
% 1.61/0.60    spl4_9 <=> v1_funct_1(sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.61/0.60  fof(f523,plain,(
% 1.61/0.60    spl4_43 <=> v2_funct_1(sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.61/0.60  fof(f749,plain,(
% 1.61/0.60    spl4_55 <=> sK2 = k2_funct_1(sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.61/0.60  fof(f871,plain,(
% 1.61/0.60    sK2 = k4_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_43 | ~spl4_55)),
% 1.61/0.60    inference(subsumption_resolution,[],[f870,f187])).
% 1.61/0.60  fof(f870,plain,(
% 1.61/0.60    sK2 = k4_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_43 | ~spl4_55)),
% 1.61/0.60    inference(subsumption_resolution,[],[f869,f156])).
% 1.61/0.60  fof(f156,plain,(
% 1.61/0.60    v1_funct_1(sK3) | ~spl4_9),
% 1.61/0.60    inference(avatar_component_clause,[],[f154])).
% 1.61/0.60  fof(f869,plain,(
% 1.61/0.60    sK2 = k4_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_43 | ~spl4_55)),
% 1.61/0.60    inference(subsumption_resolution,[],[f821,f525])).
% 1.61/0.60  fof(f525,plain,(
% 1.61/0.60    v2_funct_1(sK3) | ~spl4_43),
% 1.61/0.60    inference(avatar_component_clause,[],[f523])).
% 1.61/0.60  fof(f821,plain,(
% 1.61/0.60    sK2 = k4_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_55),
% 1.61/0.60    inference(superposition,[],[f76,f751])).
% 1.61/0.60  fof(f751,plain,(
% 1.61/0.60    sK2 = k2_funct_1(sK3) | ~spl4_55),
% 1.61/0.60    inference(avatar_component_clause,[],[f749])).
% 1.61/0.60  fof(f76,plain,(
% 1.61/0.60    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f34])).
% 1.61/0.60  fof(f34,plain,(
% 1.61/0.60    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.60    inference(flattening,[],[f33])).
% 1.61/0.60  fof(f33,plain,(
% 1.61/0.60    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.61/0.60    inference(ennf_transformation,[],[f5])).
% 1.61/0.60  fof(f5,axiom,(
% 1.61/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.61/0.60  fof(f808,plain,(
% 1.61/0.60    ~spl4_14 | ~spl4_16 | ~spl4_38 | spl4_56),
% 1.61/0.60    inference(avatar_contradiction_clause,[],[f807])).
% 1.61/0.60  fof(f807,plain,(
% 1.61/0.60    $false | (~spl4_14 | ~spl4_16 | ~spl4_38 | spl4_56)),
% 1.61/0.60    inference(subsumption_resolution,[],[f806,f201])).
% 1.61/0.60  fof(f201,plain,(
% 1.61/0.60    v5_relat_1(sK3,sK0) | ~spl4_16),
% 1.61/0.60    inference(avatar_component_clause,[],[f199])).
% 1.61/0.60  fof(f199,plain,(
% 1.61/0.60    spl4_16 <=> v5_relat_1(sK3,sK0)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.61/0.60  fof(f806,plain,(
% 1.61/0.60    ~v5_relat_1(sK3,sK0) | (~spl4_14 | ~spl4_38 | spl4_56)),
% 1.61/0.60    inference(subsumption_resolution,[],[f805,f435])).
% 1.61/0.60  fof(f435,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | ~spl4_38),
% 1.61/0.60    inference(avatar_component_clause,[],[f433])).
% 1.61/0.60  fof(f433,plain,(
% 1.61/0.60    spl4_38 <=> v2_funct_2(sK3,sK0)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.61/0.60  fof(f805,plain,(
% 1.61/0.60    ~v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | (~spl4_14 | spl4_56)),
% 1.61/0.60    inference(equality_resolution,[],[f761])).
% 1.61/0.60  fof(f761,plain,(
% 1.61/0.60    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0)) ) | (~spl4_14 | spl4_56)),
% 1.61/0.60    inference(subsumption_resolution,[],[f760,f187])).
% 1.61/0.60  fof(f760,plain,(
% 1.61/0.60    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl4_56),
% 1.61/0.60    inference(superposition,[],[f755,f101])).
% 1.61/0.60  fof(f101,plain,(
% 1.61/0.60    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f58])).
% 1.61/0.60  fof(f58,plain,(
% 1.61/0.60    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.61/0.60    inference(nnf_transformation,[],[f50])).
% 1.61/0.60  fof(f50,plain,(
% 1.61/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.61/0.60    inference(flattening,[],[f49])).
% 1.61/0.60  fof(f49,plain,(
% 1.61/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.61/0.60    inference(ennf_transformation,[],[f14])).
% 1.61/0.60  fof(f14,axiom,(
% 1.61/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.61/0.60  fof(f755,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | spl4_56),
% 1.61/0.60    inference(avatar_component_clause,[],[f753])).
% 1.61/0.60  fof(f753,plain,(
% 1.61/0.60    spl4_56 <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.61/0.60  fof(f756,plain,(
% 1.61/0.60    spl4_55 | ~spl4_56 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_40 | ~spl4_43 | ~spl4_47),
% 1.61/0.60    inference(avatar_split_clause,[],[f746,f554,f523,f454,f285,f191,f185,f169,f154,f753,f749])).
% 1.61/0.60  fof(f169,plain,(
% 1.61/0.60    spl4_12 <=> v1_funct_1(sK2)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.61/0.60  fof(f191,plain,(
% 1.61/0.60    spl4_15 <=> v1_relat_1(sK2)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.61/0.60  fof(f285,plain,(
% 1.61/0.60    spl4_25 <=> sK1 = k1_relat_1(sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.61/0.60  fof(f454,plain,(
% 1.61/0.60    spl4_40 <=> sK1 = k2_relat_1(sK2)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.61/0.60  fof(f554,plain,(
% 1.61/0.60    spl4_47 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.61/0.60  fof(f746,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_40 | ~spl4_43 | ~spl4_47)),
% 1.61/0.60    inference(subsumption_resolution,[],[f745,f456])).
% 1.61/0.60  fof(f456,plain,(
% 1.61/0.60    sK1 = k2_relat_1(sK2) | ~spl4_40),
% 1.61/0.60    inference(avatar_component_clause,[],[f454])).
% 1.61/0.60  fof(f745,plain,(
% 1.61/0.60    sK1 != k2_relat_1(sK2) | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_43 | ~spl4_47)),
% 1.61/0.60    inference(forward_demodulation,[],[f744,f287])).
% 1.61/0.60  fof(f287,plain,(
% 1.61/0.60    sK1 = k1_relat_1(sK3) | ~spl4_25),
% 1.61/0.60    inference(avatar_component_clause,[],[f285])).
% 1.61/0.60  fof(f744,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_43 | ~spl4_47)),
% 1.61/0.60    inference(subsumption_resolution,[],[f743,f187])).
% 1.61/0.60  fof(f743,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_43 | ~spl4_47)),
% 1.61/0.60    inference(subsumption_resolution,[],[f742,f156])).
% 1.61/0.60  fof(f742,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_43 | ~spl4_47)),
% 1.61/0.60    inference(subsumption_resolution,[],[f741,f193])).
% 1.61/0.60  fof(f193,plain,(
% 1.61/0.60    v1_relat_1(sK2) | ~spl4_15),
% 1.61/0.60    inference(avatar_component_clause,[],[f191])).
% 1.61/0.60  fof(f741,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_43 | ~spl4_47)),
% 1.61/0.60    inference(subsumption_resolution,[],[f740,f171])).
% 1.61/0.60  fof(f171,plain,(
% 1.61/0.60    v1_funct_1(sK2) | ~spl4_12),
% 1.61/0.60    inference(avatar_component_clause,[],[f169])).
% 1.61/0.60  fof(f740,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_43 | ~spl4_47)),
% 1.61/0.60    inference(subsumption_resolution,[],[f735,f525])).
% 1.61/0.60  fof(f735,plain,(
% 1.61/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_47),
% 1.61/0.60    inference(superposition,[],[f73,f556])).
% 1.61/0.60  fof(f556,plain,(
% 1.61/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_47),
% 1.61/0.60    inference(avatar_component_clause,[],[f554])).
% 1.61/0.60  fof(f73,plain,(
% 1.61/0.60    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f30])).
% 1.61/0.60  fof(f30,plain,(
% 1.61/0.60    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.60    inference(flattening,[],[f29])).
% 1.61/0.60  fof(f29,plain,(
% 1.61/0.60    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.61/0.60    inference(ennf_transformation,[],[f9])).
% 1.61/0.60  fof(f9,axiom,(
% 1.61/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.61/0.60  fof(f737,plain,(
% 1.61/0.60    spl4_42 | ~spl4_47),
% 1.61/0.60    inference(avatar_contradiction_clause,[],[f736])).
% 1.61/0.60  fof(f736,plain,(
% 1.61/0.60    $false | (spl4_42 | ~spl4_47)),
% 1.61/0.60    inference(subsumption_resolution,[],[f732,f88])).
% 1.61/0.60  fof(f88,plain,(
% 1.61/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f6])).
% 1.61/0.60  fof(f6,axiom,(
% 1.61/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.61/0.60  fof(f732,plain,(
% 1.61/0.60    ~v2_funct_1(k6_relat_1(sK0)) | (spl4_42 | ~spl4_47)),
% 1.61/0.60    inference(backward_demodulation,[],[f521,f556])).
% 1.61/0.60  fof(f521,plain,(
% 1.61/0.60    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_42),
% 1.61/0.60    inference(avatar_component_clause,[],[f519])).
% 1.61/0.60  fof(f519,plain,(
% 1.61/0.60    spl4_42 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.61/0.60  fof(f632,plain,(
% 1.61/0.60    spl4_47 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_45),
% 1.61/0.60    inference(avatar_split_clause,[],[f631,f545,f169,f159,f154,f144,f554])).
% 1.61/0.60  fof(f144,plain,(
% 1.61/0.60    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.61/0.60  fof(f159,plain,(
% 1.61/0.60    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.61/0.60  fof(f545,plain,(
% 1.61/0.60    spl4_45 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.61/0.60  fof(f631,plain,(
% 1.61/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_45)),
% 1.61/0.60    inference(subsumption_resolution,[],[f630,f171])).
% 1.61/0.60  fof(f630,plain,(
% 1.61/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_45)),
% 1.61/0.60    inference(subsumption_resolution,[],[f629,f161])).
% 1.61/0.60  fof(f161,plain,(
% 1.61/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.61/0.60    inference(avatar_component_clause,[],[f159])).
% 1.61/0.60  fof(f629,plain,(
% 1.61/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_45)),
% 1.61/0.60    inference(subsumption_resolution,[],[f628,f156])).
% 1.61/0.60  fof(f628,plain,(
% 1.61/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_45)),
% 1.61/0.60    inference(subsumption_resolution,[],[f619,f146])).
% 1.61/0.60  fof(f146,plain,(
% 1.61/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.61/0.60    inference(avatar_component_clause,[],[f144])).
% 1.61/0.60  fof(f619,plain,(
% 1.61/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_45),
% 1.61/0.60    inference(superposition,[],[f95,f547])).
% 1.61/0.60  fof(f547,plain,(
% 1.61/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_45),
% 1.61/0.60    inference(avatar_component_clause,[],[f545])).
% 1.61/0.60  fof(f95,plain,(
% 1.61/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f46])).
% 1.61/0.60  fof(f46,plain,(
% 1.61/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.61/0.60    inference(flattening,[],[f45])).
% 1.61/0.60  fof(f45,plain,(
% 1.61/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.61/0.60    inference(ennf_transformation,[],[f17])).
% 1.61/0.60  fof(f17,axiom,(
% 1.61/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.61/0.60  fof(f585,plain,(
% 1.61/0.60    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_44),
% 1.61/0.60    inference(avatar_contradiction_clause,[],[f584])).
% 1.61/0.60  fof(f584,plain,(
% 1.61/0.60    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_44)),
% 1.61/0.60    inference(subsumption_resolution,[],[f583,f171])).
% 1.61/0.60  fof(f583,plain,(
% 1.61/0.60    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_44)),
% 1.61/0.60    inference(subsumption_resolution,[],[f582,f161])).
% 1.61/0.60  fof(f582,plain,(
% 1.61/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_44)),
% 1.61/0.60    inference(subsumption_resolution,[],[f581,f156])).
% 1.61/0.60  fof(f581,plain,(
% 1.61/0.60    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_44)),
% 1.61/0.60    inference(subsumption_resolution,[],[f578,f146])).
% 1.61/0.60  fof(f578,plain,(
% 1.61/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_44),
% 1.61/0.60    inference(resolution,[],[f543,f94])).
% 1.61/0.60  fof(f94,plain,(
% 1.61/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f44])).
% 1.61/0.60  fof(f44,plain,(
% 1.61/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.61/0.60    inference(flattening,[],[f43])).
% 1.61/0.60  fof(f43,plain,(
% 1.61/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.61/0.60    inference(ennf_transformation,[],[f15])).
% 1.61/0.60  fof(f15,axiom,(
% 1.61/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.61/0.60  fof(f543,plain,(
% 1.61/0.60    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_44),
% 1.61/0.60    inference(avatar_component_clause,[],[f541])).
% 1.61/0.60  fof(f541,plain,(
% 1.61/0.60    spl4_44 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.61/0.60  fof(f548,plain,(
% 1.61/0.60    ~spl4_44 | spl4_45 | ~spl4_13),
% 1.61/0.60    inference(avatar_split_clause,[],[f537,f175,f545,f541])).
% 1.61/0.60  fof(f175,plain,(
% 1.61/0.60    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.61/0.60  fof(f537,plain,(
% 1.61/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.61/0.60    inference(resolution,[],[f307,f177])).
% 1.61/0.60  fof(f177,plain,(
% 1.61/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.61/0.60    inference(avatar_component_clause,[],[f175])).
% 1.61/0.60  fof(f307,plain,(
% 1.61/0.60    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.61/0.60    inference(resolution,[],[f89,f179])).
% 1.61/0.60  fof(f179,plain,(
% 1.61/0.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.61/0.60    inference(forward_demodulation,[],[f91,f92])).
% 1.61/0.60  fof(f92,plain,(
% 1.61/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f18])).
% 1.61/0.60  fof(f18,axiom,(
% 1.61/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.61/0.60  fof(f91,plain,(
% 1.61/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f23])).
% 1.61/0.60  fof(f23,plain,(
% 1.61/0.60    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.61/0.60    inference(pure_predicate_removal,[],[f16])).
% 1.61/0.60  fof(f16,axiom,(
% 1.61/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.61/0.60  fof(f89,plain,(
% 1.61/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f57])).
% 1.61/0.60  fof(f57,plain,(
% 1.61/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.60    inference(nnf_transformation,[],[f42])).
% 1.61/0.60  fof(f42,plain,(
% 1.61/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.60    inference(flattening,[],[f41])).
% 1.61/0.60  fof(f41,plain,(
% 1.61/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.61/0.60    inference(ennf_transformation,[],[f12])).
% 1.61/0.60  fof(f12,axiom,(
% 1.61/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.61/0.60  fof(f526,plain,(
% 1.61/0.60    ~spl4_42 | spl4_43 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_40),
% 1.61/0.60    inference(avatar_split_clause,[],[f517,f454,f285,f191,f185,f169,f154,f523,f519])).
% 1.61/0.60  fof(f517,plain,(
% 1.61/0.60    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_25 | ~spl4_40)),
% 1.61/0.60    inference(subsumption_resolution,[],[f516,f187])).
% 1.61/0.60  fof(f516,plain,(
% 1.61/0.60    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_25 | ~spl4_40)),
% 1.61/0.60    inference(subsumption_resolution,[],[f515,f156])).
% 1.61/0.60  fof(f515,plain,(
% 1.61/0.60    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_25 | ~spl4_40)),
% 1.61/0.60    inference(trivial_inequality_removal,[],[f514])).
% 1.61/0.60  fof(f514,plain,(
% 1.61/0.60    sK1 != sK1 | v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_25 | ~spl4_40)),
% 1.61/0.60    inference(superposition,[],[f470,f287])).
% 1.61/0.60  fof(f470,plain,(
% 1.61/0.60    ( ! [X0] : (k1_relat_1(X0) != sK1 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK2,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_12 | ~spl4_15 | ~spl4_40)),
% 1.61/0.60    inference(subsumption_resolution,[],[f469,f193])).
% 1.61/0.60  fof(f469,plain,(
% 1.61/0.60    ( ! [X0] : (k1_relat_1(X0) != sK1 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl4_12 | ~spl4_40)),
% 1.61/0.60    inference(subsumption_resolution,[],[f464,f171])).
% 1.61/0.60  fof(f464,plain,(
% 1.61/0.60    ( ! [X0] : (k1_relat_1(X0) != sK1 | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK2,X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_40),
% 1.61/0.60    inference(superposition,[],[f86,f456])).
% 1.61/0.60  fof(f86,plain,(
% 1.61/0.60    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f40])).
% 1.61/0.60  fof(f40,plain,(
% 1.61/0.60    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.60    inference(flattening,[],[f39])).
% 1.61/0.60  fof(f39,plain,(
% 1.61/0.60    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.61/0.60    inference(ennf_transformation,[],[f7])).
% 1.61/0.60  fof(f7,axiom,(
% 1.61/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.61/0.60  fof(f462,plain,(
% 1.61/0.60    spl4_40 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_36),
% 1.61/0.60    inference(avatar_split_clause,[],[f461,f405,f191,f169,f129,f454])).
% 1.61/0.60  fof(f129,plain,(
% 1.61/0.60    spl4_4 <=> v2_funct_1(sK2)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.61/0.60  fof(f405,plain,(
% 1.61/0.60    spl4_36 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.61/0.60  fof(f461,plain,(
% 1.61/0.60    sK1 = k2_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_36)),
% 1.61/0.60    inference(forward_demodulation,[],[f460,f96])).
% 1.61/0.60  fof(f96,plain,(
% 1.61/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.61/0.60    inference(cnf_transformation,[],[f4])).
% 1.61/0.60  fof(f4,axiom,(
% 1.61/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.61/0.60  fof(f460,plain,(
% 1.61/0.60    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_36)),
% 1.61/0.60    inference(subsumption_resolution,[],[f459,f193])).
% 1.61/0.60  fof(f459,plain,(
% 1.61/0.60    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_36)),
% 1.61/0.60    inference(subsumption_resolution,[],[f458,f171])).
% 1.61/0.60  fof(f458,plain,(
% 1.61/0.60    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_36)),
% 1.61/0.60    inference(subsumption_resolution,[],[f439,f131])).
% 1.61/0.60  fof(f131,plain,(
% 1.61/0.60    v2_funct_1(sK2) | ~spl4_4),
% 1.61/0.60    inference(avatar_component_clause,[],[f129])).
% 1.61/0.60  fof(f439,plain,(
% 1.61/0.60    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_36),
% 1.61/0.60    inference(superposition,[],[f74,f407])).
% 1.61/0.60  fof(f407,plain,(
% 1.61/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_36),
% 1.61/0.60    inference(avatar_component_clause,[],[f405])).
% 1.61/0.60  fof(f74,plain,(
% 1.61/0.60    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f32])).
% 1.61/0.60  fof(f32,plain,(
% 1.61/0.60    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.61/0.60    inference(flattening,[],[f31])).
% 1.61/0.60  fof(f31,plain,(
% 1.61/0.60    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.61/0.60    inference(ennf_transformation,[],[f8])).
% 1.61/0.60  fof(f8,axiom,(
% 1.61/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 1.61/0.60  fof(f436,plain,(
% 1.61/0.60    spl4_38 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.61/0.60    inference(avatar_split_clause,[],[f431,f175,f169,f164,f159,f154,f149,f144,f433])).
% 1.61/0.60  fof(f149,plain,(
% 1.61/0.60    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.61/0.60  fof(f164,plain,(
% 1.61/0.60    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.61/0.60  fof(f431,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f430,f171])).
% 1.61/0.60  fof(f430,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f429,f166])).
% 1.61/0.60  fof(f166,plain,(
% 1.61/0.60    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.61/0.60    inference(avatar_component_clause,[],[f164])).
% 1.61/0.60  fof(f429,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f428,f161])).
% 1.61/0.60  fof(f428,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f427,f156])).
% 1.61/0.60  fof(f427,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_8 | ~spl4_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f426,f151])).
% 1.61/0.60  fof(f151,plain,(
% 1.61/0.60    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.61/0.60    inference(avatar_component_clause,[],[f149])).
% 1.61/0.60  fof(f426,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.61/0.60    inference(subsumption_resolution,[],[f423,f146])).
% 1.61/0.60  fof(f423,plain,(
% 1.61/0.60    v2_funct_2(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.61/0.60    inference(resolution,[],[f422,f177])).
% 1.61/0.60  fof(f422,plain,(
% 1.61/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | v2_funct_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.61/0.60    inference(forward_demodulation,[],[f84,f92])).
% 1.61/0.60  fof(f84,plain,(
% 1.61/0.60    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f38])).
% 1.61/0.60  fof(f38,plain,(
% 1.61/0.60    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.61/0.60    inference(flattening,[],[f37])).
% 1.61/0.60  fof(f37,plain,(
% 1.61/0.60    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.61/0.60    inference(ennf_transformation,[],[f19])).
% 1.61/0.60  fof(f19,axiom,(
% 1.61/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.61/0.60  fof(f408,plain,(
% 1.61/0.60    spl4_36 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.61/0.60    inference(avatar_split_clause,[],[f403,f169,f164,f159,f139,f129,f119,f405])).
% 1.61/0.60  fof(f119,plain,(
% 1.61/0.60    spl4_2 <=> k1_xboole_0 = sK1),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.61/0.60  fof(f139,plain,(
% 1.61/0.60    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.61/0.60  fof(f403,plain,(
% 1.61/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.61/0.60    inference(subsumption_resolution,[],[f402,f171])).
% 1.61/0.60  fof(f402,plain,(
% 1.61/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.61/0.60    inference(subsumption_resolution,[],[f401,f166])).
% 1.61/0.60  fof(f401,plain,(
% 1.61/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.61/0.60    inference(subsumption_resolution,[],[f400,f161])).
% 1.61/0.60  fof(f400,plain,(
% 1.61/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.61/0.60    inference(subsumption_resolution,[],[f399,f131])).
% 1.61/0.60  fof(f399,plain,(
% 1.61/0.60    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.61/0.60    inference(subsumption_resolution,[],[f398,f121])).
% 1.61/0.60  fof(f121,plain,(
% 1.61/0.60    k1_xboole_0 != sK1 | spl4_2),
% 1.61/0.60    inference(avatar_component_clause,[],[f119])).
% 1.61/0.60  fof(f398,plain,(
% 1.61/0.60    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.61/0.60    inference(trivial_inequality_removal,[],[f397])).
% 1.61/0.60  fof(f397,plain,(
% 1.61/0.60    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.61/0.60    inference(superposition,[],[f345,f141])).
% 1.61/0.60  fof(f141,plain,(
% 1.61/0.60    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.61/0.60    inference(avatar_component_clause,[],[f139])).
% 1.61/0.60  fof(f345,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.61/0.60    inference(forward_demodulation,[],[f72,f92])).
% 1.61/0.60  fof(f72,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.61/0.60    inference(cnf_transformation,[],[f28])).
% 1.61/0.60  fof(f28,plain,(
% 1.61/0.60    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.61/0.60    inference(flattening,[],[f27])).
% 1.61/0.60  fof(f27,plain,(
% 1.61/0.60    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.61/0.60    inference(ennf_transformation,[],[f20])).
% 1.61/0.60  fof(f20,axiom,(
% 1.61/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.61/0.60  fof(f290,plain,(
% 1.61/0.60    spl4_25 | ~spl4_7 | ~spl4_23),
% 1.61/0.60    inference(avatar_split_clause,[],[f289,f266,f144,f285])).
% 1.61/0.60  fof(f266,plain,(
% 1.61/0.60    spl4_23 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.61/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.61/0.60  fof(f289,plain,(
% 1.61/0.60    sK1 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_23)),
% 1.61/0.60    inference(subsumption_resolution,[],[f281,f146])).
% 1.61/0.60  fof(f281,plain,(
% 1.61/0.60    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_23),
% 1.61/0.60    inference(superposition,[],[f100,f268])).
% 1.61/0.60  fof(f268,plain,(
% 1.61/0.60    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_23),
% 1.61/0.60    inference(avatar_component_clause,[],[f266])).
% 1.61/0.60  fof(f100,plain,(
% 1.61/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.61/0.60    inference(cnf_transformation,[],[f48])).
% 1.61/0.60  fof(f48,plain,(
% 1.61/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.60    inference(ennf_transformation,[],[f11])).
% 1.61/0.60  fof(f11,axiom,(
% 1.61/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.61/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.61/0.61  fof(f269,plain,(
% 1.61/0.61    spl4_23 | spl4_3 | ~spl4_7 | ~spl4_8),
% 1.61/0.61    inference(avatar_split_clause,[],[f264,f149,f144,f124,f266])).
% 1.61/0.61  fof(f124,plain,(
% 1.61/0.61    spl4_3 <=> k1_xboole_0 = sK0),
% 1.61/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.61/0.61  fof(f264,plain,(
% 1.61/0.61    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_3 | ~spl4_7 | ~spl4_8)),
% 1.61/0.61    inference(subsumption_resolution,[],[f263,f126])).
% 1.61/0.61  fof(f126,plain,(
% 1.61/0.61    k1_xboole_0 != sK0 | spl4_3),
% 1.61/0.61    inference(avatar_component_clause,[],[f124])).
% 1.61/0.61  fof(f263,plain,(
% 1.61/0.61    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8)),
% 1.61/0.61    inference(subsumption_resolution,[],[f260,f151])).
% 1.61/0.61  fof(f260,plain,(
% 1.61/0.61    ~v1_funct_2(sK3,sK1,sK0) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_7),
% 1.61/0.61    inference(resolution,[],[f77,f146])).
% 1.61/0.61  fof(f77,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.61/0.61    inference(cnf_transformation,[],[f56])).
% 1.61/0.61  fof(f56,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.61    inference(nnf_transformation,[],[f36])).
% 1.61/0.61  fof(f36,plain,(
% 1.61/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.61    inference(flattening,[],[f35])).
% 1.61/0.61  fof(f35,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.61    inference(ennf_transformation,[],[f13])).
% 1.61/0.61  fof(f13,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.61/0.61  fof(f218,plain,(
% 1.61/0.61    ~spl4_18 | spl4_1 | ~spl4_4 | ~spl4_12 | ~spl4_15),
% 1.61/0.61    inference(avatar_split_clause,[],[f213,f191,f169,f129,f114,f215])).
% 1.61/0.61  fof(f114,plain,(
% 1.61/0.61    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.61/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.61/0.61  fof(f213,plain,(
% 1.61/0.61    sK3 != k4_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_12 | ~spl4_15)),
% 1.61/0.61    inference(subsumption_resolution,[],[f212,f193])).
% 1.61/0.61  fof(f212,plain,(
% 1.61/0.61    sK3 != k4_relat_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4 | ~spl4_12)),
% 1.61/0.61    inference(subsumption_resolution,[],[f211,f171])).
% 1.61/0.61  fof(f211,plain,(
% 1.61/0.61    sK3 != k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_4)),
% 1.61/0.61    inference(subsumption_resolution,[],[f210,f131])).
% 1.61/0.61  fof(f210,plain,(
% 1.61/0.61    sK3 != k4_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_1),
% 1.61/0.61    inference(superposition,[],[f116,f76])).
% 1.61/0.61  fof(f116,plain,(
% 1.61/0.61    k2_funct_1(sK2) != sK3 | spl4_1),
% 1.61/0.61    inference(avatar_component_clause,[],[f114])).
% 1.61/0.61  fof(f202,plain,(
% 1.61/0.61    spl4_16 | ~spl4_7),
% 1.61/0.61    inference(avatar_split_clause,[],[f195,f144,f199])).
% 1.61/0.61  fof(f195,plain,(
% 1.61/0.61    v5_relat_1(sK3,sK0) | ~spl4_7),
% 1.61/0.61    inference(resolution,[],[f104,f146])).
% 1.61/0.61  fof(f104,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f52])).
% 1.61/0.61  fof(f52,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.61/0.61    inference(ennf_transformation,[],[f24])).
% 1.61/0.61  fof(f24,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.61/0.61    inference(pure_predicate_removal,[],[f10])).
% 1.61/0.61  fof(f10,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.61/0.61  fof(f194,plain,(
% 1.61/0.61    spl4_15 | ~spl4_10),
% 1.61/0.61    inference(avatar_split_clause,[],[f189,f159,f191])).
% 1.61/0.61  fof(f189,plain,(
% 1.61/0.61    v1_relat_1(sK2) | ~spl4_10),
% 1.61/0.61    inference(subsumption_resolution,[],[f181,f99])).
% 1.61/0.61  fof(f99,plain,(
% 1.61/0.61    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f2])).
% 1.61/0.61  fof(f2,axiom,(
% 1.61/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.61/0.61  fof(f181,plain,(
% 1.61/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 1.61/0.61    inference(resolution,[],[f98,f161])).
% 1.61/0.61  fof(f98,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f47])).
% 1.61/0.61  fof(f47,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f1])).
% 1.61/0.61  fof(f1,axiom,(
% 1.61/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.61/0.61  fof(f188,plain,(
% 1.61/0.61    spl4_14 | ~spl4_7),
% 1.61/0.61    inference(avatar_split_clause,[],[f183,f144,f185])).
% 1.61/0.61  fof(f183,plain,(
% 1.61/0.61    v1_relat_1(sK3) | ~spl4_7),
% 1.61/0.61    inference(subsumption_resolution,[],[f180,f99])).
% 1.61/0.61  fof(f180,plain,(
% 1.61/0.61    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 1.61/0.61    inference(resolution,[],[f98,f146])).
% 1.61/0.61  fof(f178,plain,(
% 1.61/0.61    spl4_13 | ~spl4_5),
% 1.61/0.61    inference(avatar_split_clause,[],[f173,f134,f175])).
% 1.61/0.61  fof(f134,plain,(
% 1.61/0.61    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.61/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.61/0.61  fof(f173,plain,(
% 1.61/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.61/0.61    inference(backward_demodulation,[],[f136,f92])).
% 1.61/0.61  fof(f136,plain,(
% 1.61/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.61/0.61    inference(avatar_component_clause,[],[f134])).
% 1.61/0.61  fof(f172,plain,(
% 1.61/0.61    spl4_12),
% 1.61/0.61    inference(avatar_split_clause,[],[f59,f169])).
% 1.61/0.61  fof(f59,plain,(
% 1.61/0.61    v1_funct_1(sK2)),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f55,plain,(
% 1.61/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.61/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f54,f53])).
% 1.61/0.61  fof(f53,plain,(
% 1.61/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f54,plain,(
% 1.61/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.61/0.61    introduced(choice_axiom,[])).
% 1.61/0.61  fof(f26,plain,(
% 1.61/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.61/0.61    inference(flattening,[],[f25])).
% 1.61/0.61  fof(f25,plain,(
% 1.61/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.61/0.61    inference(ennf_transformation,[],[f22])).
% 1.61/0.61  fof(f22,negated_conjecture,(
% 1.61/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.61/0.61    inference(negated_conjecture,[],[f21])).
% 1.61/0.61  fof(f21,conjecture,(
% 1.61/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.61/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.61/0.61  fof(f167,plain,(
% 1.61/0.61    spl4_11),
% 1.61/0.61    inference(avatar_split_clause,[],[f60,f164])).
% 1.61/0.61  fof(f60,plain,(
% 1.61/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f162,plain,(
% 1.61/0.61    spl4_10),
% 1.61/0.61    inference(avatar_split_clause,[],[f61,f159])).
% 1.61/0.61  fof(f61,plain,(
% 1.61/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f157,plain,(
% 1.61/0.61    spl4_9),
% 1.61/0.61    inference(avatar_split_clause,[],[f62,f154])).
% 1.61/0.61  fof(f62,plain,(
% 1.61/0.61    v1_funct_1(sK3)),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f152,plain,(
% 1.61/0.61    spl4_8),
% 1.61/0.61    inference(avatar_split_clause,[],[f63,f149])).
% 1.61/0.61  fof(f63,plain,(
% 1.61/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f147,plain,(
% 1.61/0.61    spl4_7),
% 1.61/0.61    inference(avatar_split_clause,[],[f64,f144])).
% 1.61/0.61  fof(f64,plain,(
% 1.61/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f142,plain,(
% 1.61/0.61    spl4_6),
% 1.61/0.61    inference(avatar_split_clause,[],[f65,f139])).
% 1.61/0.61  fof(f65,plain,(
% 1.61/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f137,plain,(
% 1.61/0.61    spl4_5),
% 1.61/0.61    inference(avatar_split_clause,[],[f66,f134])).
% 1.61/0.61  fof(f66,plain,(
% 1.61/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f132,plain,(
% 1.61/0.61    spl4_4),
% 1.61/0.61    inference(avatar_split_clause,[],[f67,f129])).
% 1.61/0.61  fof(f67,plain,(
% 1.61/0.61    v2_funct_1(sK2)),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f127,plain,(
% 1.61/0.61    ~spl4_3),
% 1.61/0.61    inference(avatar_split_clause,[],[f68,f124])).
% 1.61/0.61  fof(f68,plain,(
% 1.61/0.61    k1_xboole_0 != sK0),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f122,plain,(
% 1.61/0.61    ~spl4_2),
% 1.61/0.61    inference(avatar_split_clause,[],[f69,f119])).
% 1.61/0.61  fof(f69,plain,(
% 1.61/0.61    k1_xboole_0 != sK1),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  fof(f117,plain,(
% 1.61/0.61    ~spl4_1),
% 1.61/0.61    inference(avatar_split_clause,[],[f70,f114])).
% 1.61/0.61  fof(f70,plain,(
% 1.61/0.61    k2_funct_1(sK2) != sK3),
% 1.61/0.61    inference(cnf_transformation,[],[f55])).
% 1.61/0.61  % SZS output end Proof for theBenchmark
% 1.61/0.61  % (5460)------------------------------
% 1.61/0.61  % (5460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.61  % (5460)Termination reason: Refutation
% 1.61/0.61  
% 1.61/0.61  % (5460)Memory used [KB]: 6908
% 1.61/0.61  % (5460)Time elapsed: 0.195 s
% 1.61/0.61  % (5460)------------------------------
% 1.61/0.61  % (5460)------------------------------
% 1.61/0.61  % (5438)Success in time 0.239 s
%------------------------------------------------------------------------------
