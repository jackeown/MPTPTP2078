%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:53 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  282 ( 598 expanded)
%              Number of leaves         :   65 ( 256 expanded)
%              Depth                    :   15
%              Number of atoms          : 1274 (2964 expanded)
%              Number of equality atoms :  261 ( 770 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f912,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f163,f172,f178,f202,f244,f270,f286,f347,f373,f420,f422,f466,f475,f494,f521,f693,f708,f734,f793,f819,f899,f900,f901,f902,f903,f904,f911])).

fof(f911,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f904,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK0 != k1_relat_1(sK2)
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f903,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f902,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f901,plain,
    ( sK2 != k2_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f900,plain,
    ( sK2 != k2_funct_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f899,plain,
    ( spl4_55
    | ~ spl4_62 ),
    inference(avatar_contradiction_clause,[],[f898])).

fof(f898,plain,
    ( $false
    | spl4_55
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f897,f733])).

fof(f733,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_55 ),
    inference(avatar_component_clause,[],[f731])).

fof(f731,plain,
    ( spl4_55
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f897,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_62 ),
    inference(forward_demodulation,[],[f881,f82])).

fof(f82,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f881,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_62 ),
    inference(superposition,[],[f82,f788])).

fof(f788,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl4_62
  <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f819,plain,
    ( ~ spl4_59
    | ~ spl4_56
    | ~ spl4_60
    | spl4_65
    | ~ spl4_66
    | ~ spl4_67
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_33
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f806,f417,f388,f169,f139,f816,f812,f808,f768,f749,f764])).

fof(f764,plain,
    ( spl4_59
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f749,plain,
    ( spl4_56
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f768,plain,
    ( spl4_60
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f808,plain,
    ( spl4_65
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f812,plain,
    ( spl4_66
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f816,plain,
    ( spl4_67
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f139,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f169,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f388,plain,
    ( spl4_33
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f417,plain,
    ( spl4_37
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f806,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_33
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f805,f390])).

fof(f390,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f388])).

fof(f805,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f804,f171])).

fof(f171,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f804,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f780,f141])).

fof(f141,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f780,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_37 ),
    inference(superposition,[],[f65,f419])).

fof(f419,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f417])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
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
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f793,plain,
    ( spl4_62
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f792,f417,f396,f169,f139,f786])).

fof(f396,plain,
    ( spl4_34
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f792,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f791,f171])).

fof(f791,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f790,f141])).

fof(f790,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_34
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f777,f398])).

fof(f398,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f396])).

fof(f777,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f66,f419])).

fof(f66,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f734,plain,
    ( ~ spl4_34
    | spl4_54
    | ~ spl4_55
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_33
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f725,f472,f388,f197,f175,f169,f154,f139,f731,f727,f396])).

fof(f727,plain,
    ( spl4_54
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f154,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f175,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f197,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f472,plain,
    ( spl4_41
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f725,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_33
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f724,f199])).

fof(f199,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f724,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_33
    | ~ spl4_41 ),
    inference(trivial_inequality_removal,[],[f723])).

fof(f723,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_33
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f722,f390])).

fof(f722,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f721,f171])).

fof(f721,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f720,f141])).

fof(f720,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f719,f177])).

fof(f177,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f719,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f541,f156])).

fof(f156,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f541,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_41 ),
    inference(superposition,[],[f65,f474])).

fof(f474,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f472])).

fof(f708,plain,
    ( spl4_34
    | ~ spl4_44
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f707,f463,f154,f149,f144,f139,f134,f129,f124,f109,f579,f396])).

fof(f579,plain,
    ( spl4_44
  <=> v2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f109,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f124,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f129,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f134,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f144,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f149,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f463,plain,
    ( spl4_39
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f707,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f706,f141])).

fof(f706,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f705,f136])).

fof(f136,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f705,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f704,f131])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f704,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f566,f111])).

fof(f111,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f566,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(superposition,[],[f431,f465])).

fof(f465,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f463])).

fof(f431,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f430,f156])).

fof(f430,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f429,f151])).

fof(f151,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f429,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f428,f146])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f428,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f423])).

fof(f423,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(superposition,[],[f70,f126])).

fof(f126,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f693,plain,(
    spl4_44 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl4_44 ),
    inference(unit_resulting_resolution,[],[f95,f581,f454])).

fof(f454,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v2_funct_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f453,f82])).

fof(f453,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k6_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(subsumption_resolution,[],[f452,f86])).

fof(f86,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f452,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(subsumption_resolution,[],[f451,f87])).

fof(f87,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f451,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(trivial_inequality_removal,[],[f449])).

fof(f449,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) != k6_relat_1(X0)
      | v2_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(superposition,[],[f218,f81])).

fof(f81,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f218,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != X0
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f217,f86])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != X0
      | v2_funct_1(X0)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f216,f87])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != X0
      | v2_funct_1(X0)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != X0
      | v2_funct_1(X0)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f72,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f581,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f579])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f521,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f506])).

fof(f506,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_40 ),
    inference(unit_resulting_resolution,[],[f156,f141,f146,f131,f470,f251])).

fof(f251,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f470,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl4_40
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f494,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_38 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_38 ),
    inference(subsumption_resolution,[],[f492,f156])).

fof(f492,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_38 ),
    inference(subsumption_resolution,[],[f491,f146])).

fof(f491,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_38 ),
    inference(subsumption_resolution,[],[f490,f141])).

fof(f490,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_38 ),
    inference(subsumption_resolution,[],[f487,f131])).

fof(f487,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_38 ),
    inference(resolution,[],[f461,f78])).

fof(f461,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl4_38
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f475,plain,
    ( ~ spl4_40
    | spl4_41
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f456,f241,f472,f468])).

fof(f241,plain,
    ( spl4_19
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f456,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_19 ),
    inference(resolution,[],[f221,f243])).

fof(f243,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f241])).

fof(f221,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f73,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f466,plain,
    ( ~ spl4_38
    | spl4_39
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f455,f160,f463,f459])).

fof(f160,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f455,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f221,f162])).

fof(f162,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f422,plain,
    ( spl4_33
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f421,f370,f129,f388])).

fof(f370,plain,
    ( spl4_32
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f421,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f382,f131])).

fof(f382,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_32 ),
    inference(superposition,[],[f80,f372])).

fof(f372,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f370])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f420,plain,
    ( spl4_37
    | ~ spl4_34
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f415,f370,f139,f134,f129,f109,f396,f417])).

fof(f415,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f414,f141])).

fof(f414,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f413,f136])).

fof(f413,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f412,f131])).

fof(f412,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f383,f111])).

fof(f383,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_32 ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_32 ),
    inference(superposition,[],[f253,f372])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f63,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f373,plain,
    ( spl4_32
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f368,f160,f154,f149,f144,f139,f134,f129,f370])).

fof(f368,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f367,f141])).

fof(f367,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f366,f136])).

fof(f366,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f365,f131])).

fof(f365,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f364,f156])).

fof(f364,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f363,f151])).

fof(f363,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f359,f146])).

fof(f359,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f358,f162])).

fof(f358,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f75,f76])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f347,plain,
    ( spl4_29
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f346,f279,f342])).

fof(f342,plain,
    ( spl4_29
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f279,plain,
    ( spl4_21
  <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f346,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f334,f82])).

fof(f334,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_21 ),
    inference(superposition,[],[f82,f281])).

fof(f281,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f279])).

fof(f286,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f285,f267,f175,f154,f114,f279])).

fof(f114,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f267,plain,
    ( spl4_20
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f285,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f284,f177])).

fof(f284,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f283,f156])).

fof(f283,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f272,f116])).

fof(f116,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f272,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(superposition,[],[f66,f269])).

fof(f269,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f267])).

fof(f270,plain,
    ( spl4_20
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f265,f154,f149,f144,f124,f114,f104,f267])).

fof(f104,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f265,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f264,f156])).

fof(f264,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f263,f151])).

fof(f263,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f262,f146])).

fof(f262,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f261,f116])).

fof(f261,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f260,f106])).

fof(f106,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f260,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f257])).

fof(f257,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f253,f126])).

fof(f244,plain,
    ( spl4_19
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f239,f160,f154,f144,f139,f129,f241])).

fof(f239,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f238,f156])).

fof(f238,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f237,f146])).

fof(f237,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f236,f141])).

fof(f236,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f233,f131])).

fof(f233,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f162,f79])).

fof(f202,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f201,f144,f124,f197])).

fof(f201,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f194,f146])).

fof(f194,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f126,f80])).

fof(f178,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f173,f144,f175])).

fof(f173,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f165,f85])).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f83,f146])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f172,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f167,f129,f169])).

fof(f167,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f164,f85])).

fof(f164,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f83,f131])).

fof(f163,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f158,f119,f160])).

fof(f119,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f158,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f121,f76])).

fof(f121,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f157,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f51,f154])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f46,f45])).

fof(f45,plain,
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

fof(f46,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f152,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f52,f149])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f147,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f53,f144])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f142,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f54,f139])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f55,f134])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f129])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f127,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f57,f124])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f122,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f58,f119])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f59,f114])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f112,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f60,f109])).

fof(f60,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f104])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f62,f99])).

fof(f99,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (17828)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (17835)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.52  % (17847)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.28/0.53  % (17848)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.53  % (17840)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.53  % (17830)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.53  % (17831)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.53  % (17829)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.53  % (17851)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.54  % (17849)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.54  % (17826)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.54  % (17832)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (17845)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.28/0.54  % (17855)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.54  % (17854)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.28/0.54  % (17852)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (17827)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.54  % (17853)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.55  % (17841)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.55  % (17838)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.55  % (17846)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.55  % (17844)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.55  % (17843)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.55  % (17833)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.55  % (17839)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.55  % (17837)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.55  % (17842)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.56  % (17842)Refutation not found, incomplete strategy% (17842)------------------------------
% 1.48/0.56  % (17842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (17842)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (17842)Memory used [KB]: 10746
% 1.48/0.56  % (17842)Time elapsed: 0.149 s
% 1.48/0.56  % (17842)------------------------------
% 1.48/0.56  % (17842)------------------------------
% 1.48/0.56  % (17836)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.56  % (17850)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.56  % (17834)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.48/0.59  % (17847)Refutation found. Thanks to Tanya!
% 1.48/0.59  % SZS status Theorem for theBenchmark
% 1.48/0.60  % SZS output start Proof for theBenchmark
% 1.48/0.60  fof(f912,plain,(
% 1.48/0.60    $false),
% 1.48/0.60    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f157,f163,f172,f178,f202,f244,f270,f286,f347,f373,f420,f422,f466,f475,f494,f521,f693,f708,f734,f793,f819,f899,f900,f901,f902,f903,f904,f911])).
% 1.48/0.60  fof(f911,plain,(
% 1.48/0.60    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | k2_funct_1(sK2) = sK3),
% 1.48/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.60  fof(f904,plain,(
% 1.48/0.60    sK2 != k2_funct_1(sK3) | sK0 != k1_relat_1(sK2) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.48/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.60  fof(f903,plain,(
% 1.48/0.60    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.48/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.60  fof(f902,plain,(
% 1.48/0.60    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 1.48/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.60  fof(f901,plain,(
% 1.48/0.60    sK2 != k2_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK2)),
% 1.48/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.60  fof(f900,plain,(
% 1.48/0.60    sK2 != k2_funct_1(sK3) | v1_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK2)),
% 1.48/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.60  fof(f899,plain,(
% 1.48/0.60    spl4_55 | ~spl4_62),
% 1.48/0.60    inference(avatar_contradiction_clause,[],[f898])).
% 1.48/0.60  fof(f898,plain,(
% 1.48/0.60    $false | (spl4_55 | ~spl4_62)),
% 1.48/0.60    inference(subsumption_resolution,[],[f897,f733])).
% 1.48/0.60  fof(f733,plain,(
% 1.48/0.60    sK1 != k1_relat_1(sK3) | spl4_55),
% 1.48/0.60    inference(avatar_component_clause,[],[f731])).
% 1.48/0.60  fof(f731,plain,(
% 1.48/0.60    spl4_55 <=> sK1 = k1_relat_1(sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.48/0.60  fof(f897,plain,(
% 1.48/0.60    sK1 = k1_relat_1(sK3) | ~spl4_62),
% 1.48/0.60    inference(forward_demodulation,[],[f881,f82])).
% 1.48/0.60  fof(f82,plain,(
% 1.48/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.60    inference(cnf_transformation,[],[f4])).
% 1.48/0.60  fof(f4,axiom,(
% 1.48/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.48/0.60  fof(f881,plain,(
% 1.48/0.60    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~spl4_62),
% 1.48/0.60    inference(superposition,[],[f82,f788])).
% 1.48/0.60  fof(f788,plain,(
% 1.48/0.60    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~spl4_62),
% 1.48/0.60    inference(avatar_component_clause,[],[f786])).
% 1.48/0.60  fof(f786,plain,(
% 1.48/0.60    spl4_62 <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 1.48/0.60  fof(f819,plain,(
% 1.48/0.60    ~spl4_59 | ~spl4_56 | ~spl4_60 | spl4_65 | ~spl4_66 | ~spl4_67 | ~spl4_9 | ~spl4_14 | ~spl4_33 | ~spl4_37),
% 1.48/0.60    inference(avatar_split_clause,[],[f806,f417,f388,f169,f139,f816,f812,f808,f768,f749,f764])).
% 1.48/0.60  fof(f764,plain,(
% 1.48/0.60    spl4_59 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.48/0.60  fof(f749,plain,(
% 1.48/0.60    spl4_56 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.48/0.60  fof(f768,plain,(
% 1.48/0.60    spl4_60 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.48/0.60  fof(f808,plain,(
% 1.48/0.60    spl4_65 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.48/0.60  fof(f812,plain,(
% 1.48/0.60    spl4_66 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.48/0.60  fof(f816,plain,(
% 1.48/0.60    spl4_67 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.48/0.60  fof(f139,plain,(
% 1.48/0.60    spl4_9 <=> v1_funct_1(sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.48/0.60  fof(f169,plain,(
% 1.48/0.60    spl4_14 <=> v1_relat_1(sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.48/0.60  fof(f388,plain,(
% 1.48/0.60    spl4_33 <=> sK0 = k2_relat_1(sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.48/0.60  fof(f417,plain,(
% 1.48/0.60    spl4_37 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.48/0.60  fof(f806,plain,(
% 1.48/0.60    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_33 | ~spl4_37)),
% 1.48/0.60    inference(forward_demodulation,[],[f805,f390])).
% 1.48/0.60  fof(f390,plain,(
% 1.48/0.60    sK0 = k2_relat_1(sK3) | ~spl4_33),
% 1.48/0.60    inference(avatar_component_clause,[],[f388])).
% 1.48/0.60  fof(f805,plain,(
% 1.48/0.60    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_37)),
% 1.48/0.60    inference(subsumption_resolution,[],[f804,f171])).
% 1.48/0.60  fof(f171,plain,(
% 1.48/0.60    v1_relat_1(sK3) | ~spl4_14),
% 1.48/0.60    inference(avatar_component_clause,[],[f169])).
% 1.48/0.60  fof(f804,plain,(
% 1.48/0.60    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_37)),
% 1.48/0.60    inference(subsumption_resolution,[],[f780,f141])).
% 1.48/0.60  fof(f141,plain,(
% 1.48/0.60    v1_funct_1(sK3) | ~spl4_9),
% 1.48/0.60    inference(avatar_component_clause,[],[f139])).
% 1.48/0.60  fof(f780,plain,(
% 1.48/0.60    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_37),
% 1.48/0.60    inference(superposition,[],[f65,f419])).
% 1.48/0.60  fof(f419,plain,(
% 1.48/0.60    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_37),
% 1.48/0.60    inference(avatar_component_clause,[],[f417])).
% 1.48/0.60  fof(f65,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f26])).
% 1.48/0.60  fof(f26,plain,(
% 1.48/0.60    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.60    inference(flattening,[],[f25])).
% 1.48/0.60  fof(f25,plain,(
% 1.48/0.60    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.60    inference(ennf_transformation,[],[f9])).
% 1.48/0.60  fof(f9,axiom,(
% 1.48/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.48/0.60  fof(f793,plain,(
% 1.48/0.60    spl4_62 | ~spl4_9 | ~spl4_14 | ~spl4_34 | ~spl4_37),
% 1.48/0.60    inference(avatar_split_clause,[],[f792,f417,f396,f169,f139,f786])).
% 1.48/0.60  fof(f396,plain,(
% 1.48/0.60    spl4_34 <=> v2_funct_1(sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.48/0.60  fof(f792,plain,(
% 1.48/0.60    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_34 | ~spl4_37)),
% 1.48/0.60    inference(subsumption_resolution,[],[f791,f171])).
% 1.48/0.60  fof(f791,plain,(
% 1.48/0.60    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_34 | ~spl4_37)),
% 1.48/0.60    inference(subsumption_resolution,[],[f790,f141])).
% 1.48/0.60  fof(f790,plain,(
% 1.48/0.60    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_34 | ~spl4_37)),
% 1.48/0.60    inference(subsumption_resolution,[],[f777,f398])).
% 1.48/0.60  fof(f398,plain,(
% 1.48/0.60    v2_funct_1(sK3) | ~spl4_34),
% 1.48/0.60    inference(avatar_component_clause,[],[f396])).
% 1.48/0.60  fof(f777,plain,(
% 1.48/0.60    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_37),
% 1.48/0.60    inference(superposition,[],[f66,f419])).
% 1.48/0.60  fof(f66,plain,(
% 1.48/0.60    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f28])).
% 1.48/0.60  fof(f28,plain,(
% 1.48/0.60    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.60    inference(flattening,[],[f27])).
% 1.48/0.60  fof(f27,plain,(
% 1.48/0.60    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.60    inference(ennf_transformation,[],[f8])).
% 1.48/0.60  fof(f8,axiom,(
% 1.48/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.48/0.60  fof(f734,plain,(
% 1.48/0.60    ~spl4_34 | spl4_54 | ~spl4_55 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_33 | ~spl4_41),
% 1.48/0.60    inference(avatar_split_clause,[],[f725,f472,f388,f197,f175,f169,f154,f139,f731,f727,f396])).
% 1.48/0.60  fof(f727,plain,(
% 1.48/0.60    spl4_54 <=> sK2 = k2_funct_1(sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.48/0.60  fof(f154,plain,(
% 1.48/0.60    spl4_12 <=> v1_funct_1(sK2)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.48/0.60  fof(f175,plain,(
% 1.48/0.60    spl4_15 <=> v1_relat_1(sK2)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.48/0.60  fof(f197,plain,(
% 1.48/0.60    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.48/0.60  fof(f472,plain,(
% 1.48/0.60    spl4_41 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.48/0.60  fof(f725,plain,(
% 1.48/0.60    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_33 | ~spl4_41)),
% 1.48/0.60    inference(forward_demodulation,[],[f724,f199])).
% 1.48/0.60  fof(f199,plain,(
% 1.48/0.60    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 1.48/0.60    inference(avatar_component_clause,[],[f197])).
% 1.48/0.60  fof(f724,plain,(
% 1.48/0.60    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_33 | ~spl4_41)),
% 1.48/0.60    inference(trivial_inequality_removal,[],[f723])).
% 1.48/0.60  fof(f723,plain,(
% 1.48/0.60    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_33 | ~spl4_41)),
% 1.48/0.60    inference(forward_demodulation,[],[f722,f390])).
% 1.48/0.60  fof(f722,plain,(
% 1.48/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_41)),
% 1.48/0.60    inference(subsumption_resolution,[],[f721,f171])).
% 1.48/0.60  fof(f721,plain,(
% 1.48/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_41)),
% 1.48/0.60    inference(subsumption_resolution,[],[f720,f141])).
% 1.48/0.60  fof(f720,plain,(
% 1.48/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_41)),
% 1.48/0.60    inference(subsumption_resolution,[],[f719,f177])).
% 1.48/0.60  fof(f177,plain,(
% 1.48/0.60    v1_relat_1(sK2) | ~spl4_15),
% 1.48/0.60    inference(avatar_component_clause,[],[f175])).
% 1.48/0.60  fof(f719,plain,(
% 1.48/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_41)),
% 1.48/0.60    inference(subsumption_resolution,[],[f541,f156])).
% 1.48/0.60  fof(f156,plain,(
% 1.48/0.60    v1_funct_1(sK2) | ~spl4_12),
% 1.48/0.60    inference(avatar_component_clause,[],[f154])).
% 1.48/0.60  fof(f541,plain,(
% 1.48/0.60    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_41),
% 1.48/0.60    inference(superposition,[],[f65,f474])).
% 1.48/0.60  fof(f474,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_41),
% 1.48/0.60    inference(avatar_component_clause,[],[f472])).
% 1.48/0.60  fof(f708,plain,(
% 1.48/0.60    spl4_34 | ~spl4_44 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39),
% 1.48/0.60    inference(avatar_split_clause,[],[f707,f463,f154,f149,f144,f139,f134,f129,f124,f109,f579,f396])).
% 1.48/0.60  fof(f579,plain,(
% 1.48/0.60    spl4_44 <=> v2_funct_1(k6_relat_1(sK0))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.48/0.60  fof(f109,plain,(
% 1.48/0.60    spl4_3 <=> k1_xboole_0 = sK0),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.48/0.60  fof(f124,plain,(
% 1.48/0.60    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.48/0.60  fof(f129,plain,(
% 1.48/0.60    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.48/0.60  fof(f134,plain,(
% 1.48/0.60    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.48/0.60  fof(f144,plain,(
% 1.48/0.60    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.48/0.60  fof(f149,plain,(
% 1.48/0.60    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.48/0.60  fof(f463,plain,(
% 1.48/0.60    spl4_39 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.48/0.60  fof(f707,plain,(
% 1.48/0.60    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39)),
% 1.48/0.60    inference(subsumption_resolution,[],[f706,f141])).
% 1.48/0.60  fof(f706,plain,(
% 1.48/0.60    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39)),
% 1.48/0.60    inference(subsumption_resolution,[],[f705,f136])).
% 1.48/0.60  fof(f136,plain,(
% 1.48/0.60    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.48/0.60    inference(avatar_component_clause,[],[f134])).
% 1.48/0.60  fof(f705,plain,(
% 1.48/0.60    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39)),
% 1.48/0.60    inference(subsumption_resolution,[],[f704,f131])).
% 1.48/0.60  fof(f131,plain,(
% 1.48/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.48/0.60    inference(avatar_component_clause,[],[f129])).
% 1.48/0.60  fof(f704,plain,(
% 1.48/0.60    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39)),
% 1.48/0.60    inference(subsumption_resolution,[],[f566,f111])).
% 1.48/0.60  fof(f111,plain,(
% 1.48/0.60    k1_xboole_0 != sK0 | spl4_3),
% 1.48/0.60    inference(avatar_component_clause,[],[f109])).
% 1.48/0.60  fof(f566,plain,(
% 1.48/0.60    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39)),
% 1.48/0.60    inference(superposition,[],[f431,f465])).
% 1.48/0.60  fof(f465,plain,(
% 1.48/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_39),
% 1.48/0.60    inference(avatar_component_clause,[],[f463])).
% 1.48/0.60  fof(f431,plain,(
% 1.48/0.60    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.48/0.60    inference(subsumption_resolution,[],[f430,f156])).
% 1.48/0.60  fof(f430,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.48/0.60    inference(subsumption_resolution,[],[f429,f151])).
% 1.48/0.60  fof(f151,plain,(
% 1.48/0.60    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.48/0.60    inference(avatar_component_clause,[],[f149])).
% 1.48/0.60  fof(f429,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.48/0.60    inference(subsumption_resolution,[],[f428,f146])).
% 1.48/0.60  fof(f146,plain,(
% 1.48/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.48/0.60    inference(avatar_component_clause,[],[f144])).
% 1.48/0.60  fof(f428,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.48/0.60    inference(trivial_inequality_removal,[],[f423])).
% 1.48/0.60  fof(f423,plain,(
% 1.48/0.60    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.48/0.60    inference(superposition,[],[f70,f126])).
% 1.48/0.60  fof(f126,plain,(
% 1.48/0.60    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.48/0.60    inference(avatar_component_clause,[],[f124])).
% 1.48/0.60  fof(f70,plain,(
% 1.48/0.60    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f30])).
% 1.48/0.60  fof(f30,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.48/0.60    inference(flattening,[],[f29])).
% 1.48/0.60  fof(f29,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.48/0.60    inference(ennf_transformation,[],[f17])).
% 1.48/0.60  fof(f17,axiom,(
% 1.48/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.48/0.60  fof(f693,plain,(
% 1.48/0.60    spl4_44),
% 1.48/0.60    inference(avatar_contradiction_clause,[],[f691])).
% 1.48/0.60  fof(f691,plain,(
% 1.48/0.60    $false | spl4_44),
% 1.48/0.60    inference(unit_resulting_resolution,[],[f95,f581,f454])).
% 1.48/0.60  fof(f454,plain,(
% 1.48/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v2_funct_1(k6_relat_1(X0))) )),
% 1.48/0.60    inference(forward_demodulation,[],[f453,f82])).
% 1.48/0.60  fof(f453,plain,(
% 1.48/0.60    ( ! [X0,X1] : (v2_funct_1(k6_relat_1(X0)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 1.48/0.60    inference(subsumption_resolution,[],[f452,f86])).
% 1.48/0.60  fof(f86,plain,(
% 1.48/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.48/0.60    inference(cnf_transformation,[],[f6])).
% 1.48/0.60  fof(f6,axiom,(
% 1.48/0.60    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.48/0.60  fof(f452,plain,(
% 1.48/0.60    ( ! [X0,X1] : (v2_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 1.48/0.60    inference(subsumption_resolution,[],[f451,f87])).
% 1.48/0.60  fof(f87,plain,(
% 1.48/0.60    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.48/0.60    inference(cnf_transformation,[],[f6])).
% 1.48/0.60  fof(f451,plain,(
% 1.48/0.60    ( ! [X0,X1] : (v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 1.48/0.60    inference(trivial_inequality_removal,[],[f449])).
% 1.48/0.60  fof(f449,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k6_relat_1(X0) != k6_relat_1(X0) | v2_funct_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 1.48/0.60    inference(superposition,[],[f218,f81])).
% 1.48/0.60  fof(f81,plain,(
% 1.48/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.48/0.60    inference(cnf_transformation,[],[f4])).
% 1.48/0.60  fof(f218,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != X0 | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.48/0.60    inference(subsumption_resolution,[],[f217,f86])).
% 1.48/0.60  fof(f217,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != X0 | v2_funct_1(X0) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.48/0.60    inference(subsumption_resolution,[],[f216,f87])).
% 1.48/0.60  fof(f216,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != X0 | v2_funct_1(X0) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 1.48/0.60    inference(duplicate_literal_removal,[],[f211])).
% 1.48/0.60  fof(f211,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != X0 | v2_funct_1(X0) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 1.48/0.60    inference(superposition,[],[f72,f88])).
% 1.48/0.60  fof(f88,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f44])).
% 1.48/0.60  fof(f44,plain,(
% 1.48/0.60    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.48/0.60    inference(flattening,[],[f43])).
% 1.48/0.60  fof(f43,plain,(
% 1.48/0.60    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/0.60    inference(ennf_transformation,[],[f5])).
% 1.48/0.60  fof(f5,axiom,(
% 1.48/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.48/0.60  fof(f72,plain,(
% 1.48/0.60    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f32])).
% 1.48/0.60  fof(f32,plain,(
% 1.48/0.60    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.48/0.60    inference(flattening,[],[f31])).
% 1.48/0.60  fof(f31,plain,(
% 1.48/0.60    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.48/0.60    inference(ennf_transformation,[],[f7])).
% 1.48/0.60  fof(f7,axiom,(
% 1.48/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 1.48/0.60  fof(f581,plain,(
% 1.48/0.60    ~v2_funct_1(k6_relat_1(sK0)) | spl4_44),
% 1.48/0.60    inference(avatar_component_clause,[],[f579])).
% 1.48/0.60  fof(f95,plain,(
% 1.48/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.48/0.60    inference(equality_resolution,[],[f90])).
% 1.48/0.60  fof(f90,plain,(
% 1.48/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.48/0.60    inference(cnf_transformation,[],[f50])).
% 1.48/0.60  fof(f50,plain,(
% 1.48/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.60    inference(flattening,[],[f49])).
% 1.48/0.60  fof(f49,plain,(
% 1.48/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.48/0.60    inference(nnf_transformation,[],[f1])).
% 1.48/0.60  fof(f1,axiom,(
% 1.48/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.48/0.60  fof(f521,plain,(
% 1.48/0.60    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_40),
% 1.48/0.60    inference(avatar_contradiction_clause,[],[f506])).
% 1.48/0.60  fof(f506,plain,(
% 1.48/0.60    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_40)),
% 1.48/0.60    inference(unit_resulting_resolution,[],[f156,f141,f146,f131,f470,f251])).
% 1.48/0.60  fof(f251,plain,(
% 1.48/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.60    inference(duplicate_literal_removal,[],[f250])).
% 1.48/0.60  fof(f250,plain,(
% 1.48/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.60    inference(superposition,[],[f78,f79])).
% 1.48/0.60  fof(f79,plain,(
% 1.48/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f40])).
% 1.48/0.60  fof(f40,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.48/0.60    inference(flattening,[],[f39])).
% 1.48/0.60  fof(f39,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.48/0.60    inference(ennf_transformation,[],[f14])).
% 1.48/0.60  fof(f14,axiom,(
% 1.48/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.48/0.60  fof(f78,plain,(
% 1.48/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f38])).
% 1.48/0.60  fof(f38,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.48/0.60    inference(flattening,[],[f37])).
% 1.48/0.60  fof(f37,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.48/0.60    inference(ennf_transformation,[],[f13])).
% 1.48/0.60  fof(f13,axiom,(
% 1.48/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.48/0.60  fof(f470,plain,(
% 1.48/0.60    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_40),
% 1.48/0.60    inference(avatar_component_clause,[],[f468])).
% 1.48/0.60  fof(f468,plain,(
% 1.48/0.60    spl4_40 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.48/0.60  fof(f494,plain,(
% 1.48/0.60    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_38),
% 1.48/0.60    inference(avatar_contradiction_clause,[],[f493])).
% 1.48/0.60  fof(f493,plain,(
% 1.48/0.60    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_38)),
% 1.48/0.60    inference(subsumption_resolution,[],[f492,f156])).
% 1.48/0.60  fof(f492,plain,(
% 1.48/0.60    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_38)),
% 1.48/0.60    inference(subsumption_resolution,[],[f491,f146])).
% 1.48/0.60  fof(f491,plain,(
% 1.48/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_38)),
% 1.48/0.60    inference(subsumption_resolution,[],[f490,f141])).
% 1.48/0.60  fof(f490,plain,(
% 1.48/0.60    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_38)),
% 1.48/0.60    inference(subsumption_resolution,[],[f487,f131])).
% 1.48/0.60  fof(f487,plain,(
% 1.48/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_38),
% 1.48/0.60    inference(resolution,[],[f461,f78])).
% 1.48/0.60  fof(f461,plain,(
% 1.48/0.60    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_38),
% 1.48/0.60    inference(avatar_component_clause,[],[f459])).
% 1.48/0.60  fof(f459,plain,(
% 1.48/0.60    spl4_38 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.48/0.60  fof(f475,plain,(
% 1.48/0.60    ~spl4_40 | spl4_41 | ~spl4_19),
% 1.48/0.60    inference(avatar_split_clause,[],[f456,f241,f472,f468])).
% 1.48/0.60  fof(f241,plain,(
% 1.48/0.60    spl4_19 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.48/0.60  fof(f456,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_19),
% 1.48/0.60    inference(resolution,[],[f221,f243])).
% 1.48/0.60  fof(f243,plain,(
% 1.48/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_19),
% 1.48/0.60    inference(avatar_component_clause,[],[f241])).
% 1.48/0.60  fof(f221,plain,(
% 1.48/0.60    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.48/0.60    inference(resolution,[],[f73,f84])).
% 1.48/0.60  fof(f84,plain,(
% 1.48/0.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.48/0.60    inference(cnf_transformation,[],[f12])).
% 1.48/0.60  fof(f12,axiom,(
% 1.48/0.60    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.48/0.60  fof(f73,plain,(
% 1.48/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.60    inference(cnf_transformation,[],[f48])).
% 1.48/0.60  fof(f48,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.60    inference(nnf_transformation,[],[f34])).
% 1.48/0.60  fof(f34,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.60    inference(flattening,[],[f33])).
% 1.48/0.60  fof(f33,plain,(
% 1.48/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/0.60    inference(ennf_transformation,[],[f11])).
% 1.48/0.60  fof(f11,axiom,(
% 1.48/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.48/0.60  fof(f466,plain,(
% 1.48/0.60    ~spl4_38 | spl4_39 | ~spl4_13),
% 1.48/0.60    inference(avatar_split_clause,[],[f455,f160,f463,f459])).
% 1.48/0.60  fof(f160,plain,(
% 1.48/0.60    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.48/0.60  fof(f455,plain,(
% 1.48/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.48/0.60    inference(resolution,[],[f221,f162])).
% 1.48/0.60  fof(f162,plain,(
% 1.48/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.48/0.60    inference(avatar_component_clause,[],[f160])).
% 1.48/0.60  fof(f422,plain,(
% 1.48/0.60    spl4_33 | ~spl4_7 | ~spl4_32),
% 1.48/0.60    inference(avatar_split_clause,[],[f421,f370,f129,f388])).
% 1.48/0.60  fof(f370,plain,(
% 1.48/0.60    spl4_32 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.48/0.60  fof(f421,plain,(
% 1.48/0.60    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_32)),
% 1.48/0.60    inference(subsumption_resolution,[],[f382,f131])).
% 1.48/0.60  fof(f382,plain,(
% 1.48/0.60    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_32),
% 1.48/0.60    inference(superposition,[],[f80,f372])).
% 1.48/0.60  fof(f372,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_32),
% 1.48/0.60    inference(avatar_component_clause,[],[f370])).
% 1.48/0.60  fof(f80,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.60    inference(cnf_transformation,[],[f41])).
% 1.48/0.60  fof(f41,plain,(
% 1.48/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.60    inference(ennf_transformation,[],[f10])).
% 1.48/0.60  fof(f10,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.48/0.60  fof(f420,plain,(
% 1.48/0.60    spl4_37 | ~spl4_34 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_32),
% 1.48/0.60    inference(avatar_split_clause,[],[f415,f370,f139,f134,f129,f109,f396,f417])).
% 1.48/0.60  fof(f415,plain,(
% 1.48/0.60    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_32)),
% 1.48/0.60    inference(subsumption_resolution,[],[f414,f141])).
% 1.48/0.60  fof(f414,plain,(
% 1.48/0.60    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_32)),
% 1.48/0.60    inference(subsumption_resolution,[],[f413,f136])).
% 1.48/0.60  fof(f413,plain,(
% 1.48/0.60    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_32)),
% 1.48/0.60    inference(subsumption_resolution,[],[f412,f131])).
% 1.48/0.60  fof(f412,plain,(
% 1.48/0.60    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_32)),
% 1.48/0.60    inference(subsumption_resolution,[],[f383,f111])).
% 1.48/0.60  fof(f383,plain,(
% 1.48/0.60    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_32),
% 1.48/0.60    inference(trivial_inequality_removal,[],[f381])).
% 1.48/0.60  fof(f381,plain,(
% 1.48/0.60    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_32),
% 1.48/0.60    inference(superposition,[],[f253,f372])).
% 1.48/0.60  fof(f253,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.60    inference(forward_demodulation,[],[f63,f76])).
% 1.48/0.60  fof(f76,plain,(
% 1.48/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f15])).
% 1.48/0.60  fof(f15,axiom,(
% 1.48/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.48/0.60  fof(f63,plain,(
% 1.48/0.60    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f24])).
% 1.48/0.60  fof(f24,plain,(
% 1.48/0.60    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/0.60    inference(flattening,[],[f23])).
% 1.48/0.60  fof(f23,plain,(
% 1.48/0.60    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.48/0.60    inference(ennf_transformation,[],[f18])).
% 1.48/0.60  fof(f18,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.48/0.60  fof(f373,plain,(
% 1.48/0.60    spl4_32 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.48/0.60    inference(avatar_split_clause,[],[f368,f160,f154,f149,f144,f139,f134,f129,f370])).
% 1.48/0.60  fof(f368,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f367,f141])).
% 1.48/0.60  fof(f367,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f366,f136])).
% 1.48/0.60  fof(f366,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f365,f131])).
% 1.48/0.60  fof(f365,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f364,f156])).
% 1.48/0.60  fof(f364,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f363,f151])).
% 1.48/0.60  fof(f363,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f359,f146])).
% 1.48/0.60  fof(f359,plain,(
% 1.48/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 1.48/0.60    inference(resolution,[],[f358,f162])).
% 1.48/0.60  fof(f358,plain,(
% 1.48/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.60    inference(forward_demodulation,[],[f75,f76])).
% 1.48/0.60  fof(f75,plain,(
% 1.48/0.60    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.48/0.60    inference(cnf_transformation,[],[f36])).
% 1.48/0.60  fof(f36,plain,(
% 1.48/0.60    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.48/0.60    inference(flattening,[],[f35])).
% 1.48/0.60  fof(f35,plain,(
% 1.48/0.60    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.48/0.60    inference(ennf_transformation,[],[f16])).
% 1.48/0.60  fof(f16,axiom,(
% 1.48/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.48/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.48/0.60  fof(f347,plain,(
% 1.48/0.60    spl4_29 | ~spl4_21),
% 1.48/0.60    inference(avatar_split_clause,[],[f346,f279,f342])).
% 1.48/0.60  fof(f342,plain,(
% 1.48/0.60    spl4_29 <=> sK0 = k1_relat_1(sK2)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.48/0.60  fof(f279,plain,(
% 1.48/0.60    spl4_21 <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.48/0.60  fof(f346,plain,(
% 1.48/0.60    sK0 = k1_relat_1(sK2) | ~spl4_21),
% 1.48/0.60    inference(forward_demodulation,[],[f334,f82])).
% 1.48/0.60  fof(f334,plain,(
% 1.48/0.60    k1_relat_1(sK2) = k2_relat_1(k6_relat_1(sK0)) | ~spl4_21),
% 1.48/0.60    inference(superposition,[],[f82,f281])).
% 1.48/0.60  fof(f281,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~spl4_21),
% 1.48/0.60    inference(avatar_component_clause,[],[f279])).
% 1.48/0.60  fof(f286,plain,(
% 1.48/0.60    spl4_21 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_20),
% 1.48/0.60    inference(avatar_split_clause,[],[f285,f267,f175,f154,f114,f279])).
% 1.48/0.60  fof(f114,plain,(
% 1.48/0.60    spl4_4 <=> v2_funct_1(sK2)),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.48/0.60  fof(f267,plain,(
% 1.48/0.60    spl4_20 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.48/0.60  fof(f285,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_20)),
% 1.48/0.60    inference(subsumption_resolution,[],[f284,f177])).
% 1.48/0.60  fof(f284,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_20)),
% 1.48/0.60    inference(subsumption_resolution,[],[f283,f156])).
% 1.48/0.60  fof(f283,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_20)),
% 1.48/0.60    inference(subsumption_resolution,[],[f272,f116])).
% 1.48/0.60  fof(f116,plain,(
% 1.48/0.60    v2_funct_1(sK2) | ~spl4_4),
% 1.48/0.60    inference(avatar_component_clause,[],[f114])).
% 1.48/0.60  fof(f272,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_20),
% 1.48/0.60    inference(superposition,[],[f66,f269])).
% 1.48/0.60  fof(f269,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_20),
% 1.48/0.60    inference(avatar_component_clause,[],[f267])).
% 1.48/0.60  fof(f270,plain,(
% 1.48/0.60    spl4_20 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.48/0.60    inference(avatar_split_clause,[],[f265,f154,f149,f144,f124,f114,f104,f267])).
% 1.48/0.60  fof(f104,plain,(
% 1.48/0.60    spl4_2 <=> k1_xboole_0 = sK1),
% 1.48/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.48/0.60  fof(f265,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.48/0.60    inference(subsumption_resolution,[],[f264,f156])).
% 1.48/0.60  fof(f264,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.48/0.60    inference(subsumption_resolution,[],[f263,f151])).
% 1.48/0.60  fof(f263,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.48/0.60    inference(subsumption_resolution,[],[f262,f146])).
% 1.48/0.60  fof(f262,plain,(
% 1.48/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.48/0.60    inference(subsumption_resolution,[],[f261,f116])).
% 1.48/0.60  fof(f261,plain,(
% 1.48/0.60    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.48/0.60    inference(subsumption_resolution,[],[f260,f106])).
% 1.48/0.60  fof(f106,plain,(
% 1.48/0.60    k1_xboole_0 != sK1 | spl4_2),
% 1.48/0.60    inference(avatar_component_clause,[],[f104])).
% 1.48/0.60  fof(f260,plain,(
% 1.48/0.60    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.48/0.60    inference(trivial_inequality_removal,[],[f257])).
% 1.48/0.60  fof(f257,plain,(
% 1.48/0.60    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.48/0.60    inference(superposition,[],[f253,f126])).
% 1.48/0.60  fof(f244,plain,(
% 1.48/0.60    spl4_19 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.48/0.60    inference(avatar_split_clause,[],[f239,f160,f154,f144,f139,f129,f241])).
% 1.48/0.60  fof(f239,plain,(
% 1.48/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f238,f156])).
% 1.48/0.60  fof(f238,plain,(
% 1.48/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f237,f146])).
% 1.48/0.60  fof(f237,plain,(
% 1.48/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f236,f141])).
% 1.48/0.60  fof(f236,plain,(
% 1.48/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.48/0.60    inference(subsumption_resolution,[],[f233,f131])).
% 1.48/0.60  fof(f233,plain,(
% 1.48/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.48/0.60    inference(superposition,[],[f162,f79])).
% 1.48/0.60  fof(f202,plain,(
% 1.48/0.60    spl4_18 | ~spl4_6 | ~spl4_10),
% 1.48/0.60    inference(avatar_split_clause,[],[f201,f144,f124,f197])).
% 1.48/0.60  fof(f201,plain,(
% 1.48/0.60    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 1.48/0.60    inference(subsumption_resolution,[],[f194,f146])).
% 1.48/0.60  fof(f194,plain,(
% 1.48/0.60    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 1.48/0.60    inference(superposition,[],[f126,f80])).
% 1.48/0.60  fof(f178,plain,(
% 1.48/0.60    spl4_15 | ~spl4_10),
% 1.48/0.60    inference(avatar_split_clause,[],[f173,f144,f175])).
% 1.48/0.60  fof(f173,plain,(
% 1.48/0.60    v1_relat_1(sK2) | ~spl4_10),
% 1.48/0.60    inference(subsumption_resolution,[],[f165,f85])).
% 1.48/0.60  fof(f85,plain,(
% 1.48/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.48/0.60    inference(cnf_transformation,[],[f3])).
% 1.48/0.61  fof(f3,axiom,(
% 1.48/0.61    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.48/0.61  fof(f165,plain,(
% 1.48/0.61    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 1.48/0.61    inference(resolution,[],[f83,f146])).
% 1.48/0.61  fof(f83,plain,(
% 1.48/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.48/0.61    inference(cnf_transformation,[],[f42])).
% 1.48/0.61  fof(f42,plain,(
% 1.48/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.48/0.61    inference(ennf_transformation,[],[f2])).
% 1.48/0.61  fof(f2,axiom,(
% 1.48/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.48/0.61  fof(f172,plain,(
% 1.48/0.61    spl4_14 | ~spl4_7),
% 1.48/0.61    inference(avatar_split_clause,[],[f167,f129,f169])).
% 1.48/0.61  fof(f167,plain,(
% 1.48/0.61    v1_relat_1(sK3) | ~spl4_7),
% 1.48/0.61    inference(subsumption_resolution,[],[f164,f85])).
% 1.48/0.61  fof(f164,plain,(
% 1.48/0.61    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 1.48/0.61    inference(resolution,[],[f83,f131])).
% 1.48/0.61  fof(f163,plain,(
% 1.48/0.61    spl4_13 | ~spl4_5),
% 1.48/0.61    inference(avatar_split_clause,[],[f158,f119,f160])).
% 1.48/0.61  fof(f119,plain,(
% 1.48/0.61    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.48/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.48/0.61  fof(f158,plain,(
% 1.48/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.48/0.61    inference(backward_demodulation,[],[f121,f76])).
% 1.48/0.61  fof(f121,plain,(
% 1.48/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.48/0.61    inference(avatar_component_clause,[],[f119])).
% 1.48/0.61  fof(f157,plain,(
% 1.48/0.61    spl4_12),
% 1.48/0.61    inference(avatar_split_clause,[],[f51,f154])).
% 1.48/0.61  fof(f51,plain,(
% 1.48/0.61    v1_funct_1(sK2)),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f47,plain,(
% 1.48/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.48/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f46,f45])).
% 1.48/0.61  fof(f45,plain,(
% 1.48/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f46,plain,(
% 1.48/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.48/0.61    introduced(choice_axiom,[])).
% 1.48/0.61  fof(f22,plain,(
% 1.48/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.48/0.61    inference(flattening,[],[f21])).
% 1.48/0.61  fof(f21,plain,(
% 1.48/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.48/0.61    inference(ennf_transformation,[],[f20])).
% 1.48/0.61  fof(f20,negated_conjecture,(
% 1.48/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.48/0.61    inference(negated_conjecture,[],[f19])).
% 1.48/0.61  fof(f19,conjecture,(
% 1.48/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.48/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.48/0.61  fof(f152,plain,(
% 1.48/0.61    spl4_11),
% 1.48/0.61    inference(avatar_split_clause,[],[f52,f149])).
% 1.48/0.61  fof(f52,plain,(
% 1.48/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f147,plain,(
% 1.48/0.61    spl4_10),
% 1.48/0.61    inference(avatar_split_clause,[],[f53,f144])).
% 1.48/0.61  fof(f53,plain,(
% 1.48/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f142,plain,(
% 1.48/0.61    spl4_9),
% 1.48/0.61    inference(avatar_split_clause,[],[f54,f139])).
% 1.48/0.61  fof(f54,plain,(
% 1.48/0.61    v1_funct_1(sK3)),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f137,plain,(
% 1.48/0.61    spl4_8),
% 1.48/0.61    inference(avatar_split_clause,[],[f55,f134])).
% 1.48/0.61  fof(f55,plain,(
% 1.48/0.61    v1_funct_2(sK3,sK1,sK0)),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f132,plain,(
% 1.48/0.61    spl4_7),
% 1.48/0.61    inference(avatar_split_clause,[],[f56,f129])).
% 1.48/0.61  fof(f56,plain,(
% 1.48/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f127,plain,(
% 1.48/0.61    spl4_6),
% 1.48/0.61    inference(avatar_split_clause,[],[f57,f124])).
% 1.48/0.61  fof(f57,plain,(
% 1.48/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f122,plain,(
% 1.48/0.61    spl4_5),
% 1.48/0.61    inference(avatar_split_clause,[],[f58,f119])).
% 1.48/0.61  fof(f58,plain,(
% 1.48/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f117,plain,(
% 1.48/0.61    spl4_4),
% 1.48/0.61    inference(avatar_split_clause,[],[f59,f114])).
% 1.48/0.61  fof(f59,plain,(
% 1.48/0.61    v2_funct_1(sK2)),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f112,plain,(
% 1.48/0.61    ~spl4_3),
% 1.48/0.61    inference(avatar_split_clause,[],[f60,f109])).
% 1.48/0.61  fof(f60,plain,(
% 1.48/0.61    k1_xboole_0 != sK0),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f107,plain,(
% 1.48/0.61    ~spl4_2),
% 1.48/0.61    inference(avatar_split_clause,[],[f61,f104])).
% 1.48/0.61  fof(f61,plain,(
% 1.48/0.61    k1_xboole_0 != sK1),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  fof(f102,plain,(
% 1.48/0.61    ~spl4_1),
% 1.48/0.61    inference(avatar_split_clause,[],[f62,f99])).
% 1.48/0.61  fof(f99,plain,(
% 1.48/0.61    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.48/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.48/0.61  fof(f62,plain,(
% 1.48/0.61    k2_funct_1(sK2) != sK3),
% 1.48/0.61    inference(cnf_transformation,[],[f47])).
% 1.48/0.61  % SZS output end Proof for theBenchmark
% 1.48/0.61  % (17847)------------------------------
% 1.48/0.61  % (17847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.61  % (17847)Termination reason: Refutation
% 1.48/0.61  
% 1.48/0.61  % (17847)Memory used [KB]: 7291
% 1.48/0.61  % (17847)Time elapsed: 0.160 s
% 1.48/0.61  % (17847)------------------------------
% 1.48/0.61  % (17847)------------------------------
% 1.48/0.61  % (17817)Success in time 0.25 s
%------------------------------------------------------------------------------
