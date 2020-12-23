%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:02 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 526 expanded)
%              Number of leaves         :   57 ( 231 expanded)
%              Depth                    :   20
%              Number of atoms          : 1169 (2785 expanded)
%              Number of equality atoms :  237 ( 730 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f614,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f148,f158,f164,f187,f202,f226,f243,f305,f352,f354,f406,f449,f484,f500,f567,f569,f593,f604,f605,f606,f607,f613])).

fof(f613,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f607,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK0 != k1_relat_1(sK2)
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f606,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f605,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f604,plain,
    ( sK2 != k2_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f593,plain,
    ( ~ spl4_49
    | ~ spl4_46
    | ~ spl4_50
    | spl4_51
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_30
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f572,f349,f320,f155,f124,f590,f586,f582,f578,f527,f574])).

fof(f574,plain,
    ( spl4_49
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f527,plain,
    ( spl4_46
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f578,plain,
    ( spl4_50
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f582,plain,
    ( spl4_51
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f586,plain,
    ( spl4_52
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f590,plain,
    ( spl4_53
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f124,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f155,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f320,plain,
    ( spl4_30
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f349,plain,
    ( spl4_34
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f572,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_30
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f571,f322])).

fof(f322,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f320])).

fof(f571,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f570,f157])).

fof(f157,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f570,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f554,f126])).

fof(f126,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f554,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_34 ),
    inference(superposition,[],[f57,f351])).

fof(f351,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f349])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f569,plain,
    ( spl4_43
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f558,f349,f328,f155,f124,f481])).

fof(f481,plain,
    ( spl4_43
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f328,plain,
    ( spl4_31
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f558,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f557,f76])).

fof(f76,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f557,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f556,f157])).

fof(f556,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f555,f126])).

fof(f555,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f550,f330])).

fof(f330,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f328])).

fof(f550,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_34 ),
    inference(superposition,[],[f59,f351])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f567,plain,
    ( sK2 != k2_funct_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f500,plain,
    ( spl4_31
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f499,f403,f139,f134,f129,f124,f119,f114,f109,f94,f328])).

fof(f94,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f109,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f114,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f119,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f129,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f134,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f139,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f403,plain,
    ( spl4_39
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f499,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f498,f65])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f498,plain,
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
    inference(forward_demodulation,[],[f497,f405])).

fof(f405,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f403])).

fof(f497,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f496,f126])).

fof(f496,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f495,f121])).

fof(f121,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f495,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f375,f96])).

fof(f96,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f375,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f372,f116])).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f372,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f371,f141])).

fof(f141,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f371,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f370,f131])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f370,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f369])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(superposition,[],[f363,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f363,plain,
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
    inference(subsumption_resolution,[],[f362,f141])).

fof(f362,plain,
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
    inference(subsumption_resolution,[],[f361,f136])).

fof(f136,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f361,plain,
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
    inference(subsumption_resolution,[],[f360,f131])).

fof(f360,plain,
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
    inference(trivial_inequality_removal,[],[f355])).

fof(f355,plain,
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
    inference(superposition,[],[f62,f111])).

fof(f111,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f484,plain,
    ( ~ spl4_31
    | spl4_42
    | ~ spl4_43
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_30
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f475,f403,f320,f182,f161,f155,f139,f124,f481,f477,f328])).

fof(f477,plain,
    ( spl4_42
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f161,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f182,plain,
    ( spl4_18
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f475,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_30
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f474,f184])).

fof(f184,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f474,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_30
    | ~ spl4_39 ),
    inference(trivial_inequality_removal,[],[f473])).

fof(f473,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_30
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f472,f322])).

fof(f472,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f471,f157])).

fof(f471,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f470,f126])).

fof(f470,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f469,f163])).

fof(f163,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f469,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f464,f141])).

fof(f464,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_39 ),
    inference(superposition,[],[f57,f405])).

fof(f449,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_38 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_38 ),
    inference(unit_resulting_resolution,[],[f141,f126,f131,f116,f401,f207])).

fof(f207,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
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
    inference(superposition,[],[f72,f73])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f401,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl4_38
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f406,plain,
    ( ~ spl4_38
    | spl4_39
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f387,f199,f403,f399])).

fof(f199,plain,
    ( spl4_19
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f387,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_19 ),
    inference(resolution,[],[f190,f201])).

fof(f201,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f190,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f66,f149])).

fof(f149,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f69,f70])).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f354,plain,
    ( spl4_30
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f353,f302,f114,f320])).

fof(f302,plain,
    ( spl4_29
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f353,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f314,f116])).

fof(f314,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_29 ),
    inference(superposition,[],[f74,f304])).

fof(f304,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f302])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f352,plain,
    ( spl4_34
    | ~ spl4_31
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f347,f302,f124,f119,f114,f94,f328,f349])).

fof(f347,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f346,f126])).

fof(f346,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f345,f121])).

fof(f345,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f344,f116])).

fof(f344,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f315,f96])).

fof(f315,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_29 ),
    inference(trivial_inequality_removal,[],[f313])).

fof(f313,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_29 ),
    inference(superposition,[],[f209,f304])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f55,f70])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f305,plain,
    ( spl4_29
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f300,f145,f139,f134,f129,f124,f119,f114,f302])).

fof(f145,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f300,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f299,f126])).

fof(f299,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f298,f121])).

fof(f298,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f297,f116])).

fof(f297,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f296,f141])).

fof(f296,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f295,f136])).

fof(f295,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f292,f131])).

fof(f292,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f290,f147])).

fof(f147,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f290,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f68,f70])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f243,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f242,f223,f161,f139,f99,f235])).

fof(f235,plain,
    ( spl4_21
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f99,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f223,plain,
    ( spl4_20
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f242,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f241,f75])).

fof(f75,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f241,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f240,f163])).

fof(f240,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f239,f141])).

fof(f239,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f228,f101])).

fof(f101,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f228,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(superposition,[],[f58,f225])).

fof(f225,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f223])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f226,plain,
    ( spl4_20
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f221,f139,f134,f129,f109,f99,f89,f223])).

fof(f89,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f221,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f220,f141])).

fof(f220,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f219,f136])).

fof(f219,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f218,f131])).

fof(f218,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f217,f101])).

fof(f217,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f216,f91])).

fof(f91,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f216,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f213])).

fof(f213,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f209,f111])).

fof(f202,plain,
    ( spl4_19
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f197,f145,f139,f129,f124,f114,f199])).

fof(f197,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f196,f141])).

fof(f196,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f195,f131])).

fof(f195,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f194,f126])).

fof(f194,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f191,f116])).

fof(f191,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f147,f73])).

fof(f187,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f186,f129,f109,f182])).

fof(f186,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f179,f131])).

fof(f179,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f111,f74])).

fof(f164,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f159,f129,f161])).

fof(f159,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f151,f78])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f151,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f77,f131])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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

fof(f158,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f153,f114,f155])).

fof(f153,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f150,f78])).

fof(f150,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f77,f116])).

fof(f148,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f143,f104,f145])).

fof(f104,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f143,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f106,f70])).

fof(f106,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f142,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f43,f139])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f40,f39])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f137,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f44,f134])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f45,f129])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f127,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f46,f124])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f122,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f47,f119])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f48,f114])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f49,f109])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f50,f104])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f89])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f84])).

fof(f84,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f54,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (31703)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (31696)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (31692)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (31711)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (31691)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.55  % (31717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.55  % (31716)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.56  % (31707)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.56  % (31698)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.56  % (31708)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.56  % (31689)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.57  % (31699)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.63/0.57  % (31717)Refutation not found, incomplete strategy% (31717)------------------------------
% 1.63/0.57  % (31717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (31717)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (31717)Memory used [KB]: 11001
% 1.63/0.57  % (31717)Time elapsed: 0.173 s
% 1.63/0.57  % (31717)------------------------------
% 1.63/0.57  % (31717)------------------------------
% 1.63/0.58  % (31695)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.63/0.58  % (31690)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.63/0.58  % (31701)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.63/0.58  % (31698)Refutation not found, incomplete strategy% (31698)------------------------------
% 1.63/0.58  % (31698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (31712)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.59  % (31698)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.59  
% 1.63/0.59  % (31698)Memory used [KB]: 11001
% 1.63/0.59  % (31698)Time elapsed: 0.163 s
% 1.63/0.59  % (31698)------------------------------
% 1.63/0.59  % (31698)------------------------------
% 1.63/0.59  % (31709)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.63/0.59  % (31688)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.59  % (31715)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.63/0.59  % (31693)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.60  % (31710)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.63/0.60  % (31706)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.60  % (31713)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.63/0.60  % (31704)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.63/0.61  % (31718)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.61  % (31697)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.63/0.61  % (31702)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.63/0.61  % (31700)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.63/0.62  % (31705)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.62  % (31694)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.63  % (31704)Refutation not found, incomplete strategy% (31704)------------------------------
% 1.63/0.63  % (31704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.63  % (31704)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.63  
% 1.63/0.63  % (31704)Memory used [KB]: 10746
% 1.63/0.63  % (31704)Time elapsed: 0.209 s
% 1.63/0.63  % (31704)------------------------------
% 1.63/0.63  % (31704)------------------------------
% 1.63/0.63  % (31709)Refutation found. Thanks to Tanya!
% 1.63/0.63  % SZS status Theorem for theBenchmark
% 1.63/0.65  % SZS output start Proof for theBenchmark
% 1.63/0.65  fof(f614,plain,(
% 1.63/0.65    $false),
% 1.63/0.65    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f148,f158,f164,f187,f202,f226,f243,f305,f352,f354,f406,f449,f484,f500,f567,f569,f593,f604,f605,f606,f607,f613])).
% 1.63/0.65  fof(f613,plain,(
% 1.63/0.65    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | k2_funct_1(sK2) = sK3),
% 1.63/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.65  fof(f607,plain,(
% 1.63/0.65    sK2 != k2_funct_1(sK3) | sK0 != k1_relat_1(sK2) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.63/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.65  fof(f606,plain,(
% 1.63/0.65    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.63/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.65  fof(f605,plain,(
% 1.63/0.65    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 1.63/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.65  fof(f604,plain,(
% 1.63/0.65    sK2 != k2_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK2)),
% 1.63/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.65  fof(f593,plain,(
% 1.63/0.65    ~spl4_49 | ~spl4_46 | ~spl4_50 | spl4_51 | ~spl4_52 | ~spl4_53 | ~spl4_9 | ~spl4_14 | ~spl4_30 | ~spl4_34),
% 1.63/0.65    inference(avatar_split_clause,[],[f572,f349,f320,f155,f124,f590,f586,f582,f578,f527,f574])).
% 1.63/0.65  fof(f574,plain,(
% 1.63/0.65    spl4_49 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.63/0.65  fof(f527,plain,(
% 1.63/0.65    spl4_46 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.63/0.65  fof(f578,plain,(
% 1.63/0.65    spl4_50 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.63/0.65  fof(f582,plain,(
% 1.63/0.65    spl4_51 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.63/0.65  fof(f586,plain,(
% 1.63/0.65    spl4_52 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.63/0.65  fof(f590,plain,(
% 1.63/0.65    spl4_53 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.63/0.65  fof(f124,plain,(
% 1.63/0.65    spl4_9 <=> v1_funct_1(sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.63/0.65  fof(f155,plain,(
% 1.63/0.65    spl4_14 <=> v1_relat_1(sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.63/0.65  fof(f320,plain,(
% 1.63/0.65    spl4_30 <=> sK0 = k2_relat_1(sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.63/0.65  fof(f349,plain,(
% 1.63/0.65    spl4_34 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.63/0.65  fof(f572,plain,(
% 1.63/0.65    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_30 | ~spl4_34)),
% 1.63/0.65    inference(forward_demodulation,[],[f571,f322])).
% 1.63/0.65  fof(f322,plain,(
% 1.63/0.65    sK0 = k2_relat_1(sK3) | ~spl4_30),
% 1.63/0.65    inference(avatar_component_clause,[],[f320])).
% 1.63/0.65  fof(f571,plain,(
% 1.63/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_34)),
% 1.63/0.65    inference(subsumption_resolution,[],[f570,f157])).
% 1.63/0.65  fof(f157,plain,(
% 1.63/0.65    v1_relat_1(sK3) | ~spl4_14),
% 1.63/0.65    inference(avatar_component_clause,[],[f155])).
% 1.63/0.65  fof(f570,plain,(
% 1.63/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_34)),
% 1.63/0.65    inference(subsumption_resolution,[],[f554,f126])).
% 1.63/0.65  fof(f126,plain,(
% 1.63/0.65    v1_funct_1(sK3) | ~spl4_9),
% 1.63/0.65    inference(avatar_component_clause,[],[f124])).
% 1.63/0.65  fof(f554,plain,(
% 1.63/0.65    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_34),
% 1.63/0.65    inference(superposition,[],[f57,f351])).
% 1.63/0.65  fof(f351,plain,(
% 1.63/0.65    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_34),
% 1.63/0.65    inference(avatar_component_clause,[],[f349])).
% 1.63/0.65  fof(f57,plain,(
% 1.63/0.65    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f24])).
% 1.63/0.65  fof(f24,plain,(
% 1.63/0.65    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.63/0.65    inference(flattening,[],[f23])).
% 1.63/0.65  fof(f23,plain,(
% 1.63/0.65    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.63/0.65    inference(ennf_transformation,[],[f6])).
% 1.63/0.65  fof(f6,axiom,(
% 1.63/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.63/0.65  fof(f569,plain,(
% 1.63/0.65    spl4_43 | ~spl4_9 | ~spl4_14 | ~spl4_31 | ~spl4_34),
% 1.63/0.65    inference(avatar_split_clause,[],[f558,f349,f328,f155,f124,f481])).
% 1.63/0.65  fof(f481,plain,(
% 1.63/0.65    spl4_43 <=> sK1 = k1_relat_1(sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.63/0.65  fof(f328,plain,(
% 1.63/0.65    spl4_31 <=> v2_funct_1(sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.63/0.65  fof(f558,plain,(
% 1.63/0.65    sK1 = k1_relat_1(sK3) | (~spl4_9 | ~spl4_14 | ~spl4_31 | ~spl4_34)),
% 1.63/0.65    inference(forward_demodulation,[],[f557,f76])).
% 1.63/0.65  fof(f76,plain,(
% 1.63/0.65    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.63/0.65    inference(cnf_transformation,[],[f3])).
% 1.63/0.65  fof(f3,axiom,(
% 1.63/0.65    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.63/0.65  fof(f557,plain,(
% 1.63/0.65    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | (~spl4_9 | ~spl4_14 | ~spl4_31 | ~spl4_34)),
% 1.63/0.65    inference(subsumption_resolution,[],[f556,f157])).
% 1.63/0.65  fof(f556,plain,(
% 1.63/0.65    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_31 | ~spl4_34)),
% 1.63/0.65    inference(subsumption_resolution,[],[f555,f126])).
% 1.63/0.65  fof(f555,plain,(
% 1.63/0.65    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_31 | ~spl4_34)),
% 1.63/0.65    inference(subsumption_resolution,[],[f550,f330])).
% 1.63/0.65  fof(f330,plain,(
% 1.63/0.65    v2_funct_1(sK3) | ~spl4_31),
% 1.63/0.65    inference(avatar_component_clause,[],[f328])).
% 1.63/0.65  fof(f550,plain,(
% 1.63/0.65    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_34),
% 1.63/0.65    inference(superposition,[],[f59,f351])).
% 1.63/0.65  fof(f59,plain,(
% 1.63/0.65    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f26])).
% 1.63/0.65  fof(f26,plain,(
% 1.63/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.63/0.65    inference(flattening,[],[f25])).
% 1.63/0.65  fof(f25,plain,(
% 1.63/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.63/0.65    inference(ennf_transformation,[],[f5])).
% 1.63/0.65  fof(f5,axiom,(
% 1.63/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.63/0.65  fof(f567,plain,(
% 1.63/0.65    sK2 != k2_funct_1(sK3) | v1_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK2)),
% 1.63/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.63/0.65  fof(f500,plain,(
% 1.63/0.65    spl4_31 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39),
% 1.63/0.65    inference(avatar_split_clause,[],[f499,f403,f139,f134,f129,f124,f119,f114,f109,f94,f328])).
% 1.63/0.65  fof(f94,plain,(
% 1.63/0.65    spl4_3 <=> k1_xboole_0 = sK0),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.63/0.65  fof(f109,plain,(
% 1.63/0.65    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.63/0.65  fof(f114,plain,(
% 1.63/0.65    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.63/0.65  fof(f119,plain,(
% 1.63/0.65    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.63/0.65  fof(f129,plain,(
% 1.63/0.65    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.63/0.65  fof(f134,plain,(
% 1.63/0.65    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.63/0.65  fof(f139,plain,(
% 1.63/0.65    spl4_12 <=> v1_funct_1(sK2)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.63/0.65  fof(f403,plain,(
% 1.63/0.65    spl4_39 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.63/0.65  fof(f499,plain,(
% 1.63/0.65    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39)),
% 1.63/0.65    inference(subsumption_resolution,[],[f498,f65])).
% 1.63/0.65  fof(f65,plain,(
% 1.63/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.63/0.65    inference(cnf_transformation,[],[f4])).
% 1.63/0.65  fof(f4,axiom,(
% 1.63/0.65    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.63/0.65  fof(f498,plain,(
% 1.63/0.65    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_39)),
% 1.63/0.65    inference(forward_demodulation,[],[f497,f405])).
% 1.63/0.65  fof(f405,plain,(
% 1.63/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_39),
% 1.63/0.65    inference(avatar_component_clause,[],[f403])).
% 1.63/0.65  fof(f497,plain,(
% 1.63/0.65    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(subsumption_resolution,[],[f496,f126])).
% 1.63/0.65  fof(f496,plain,(
% 1.63/0.65    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(subsumption_resolution,[],[f495,f121])).
% 1.63/0.65  fof(f121,plain,(
% 1.63/0.65    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.63/0.65    inference(avatar_component_clause,[],[f119])).
% 1.63/0.65  fof(f495,plain,(
% 1.63/0.65    v2_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(subsumption_resolution,[],[f375,f96])).
% 1.63/0.65  fof(f96,plain,(
% 1.63/0.65    k1_xboole_0 != sK0 | spl4_3),
% 1.63/0.65    inference(avatar_component_clause,[],[f94])).
% 1.63/0.65  fof(f375,plain,(
% 1.63/0.65    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(resolution,[],[f372,f116])).
% 1.63/0.65  fof(f116,plain,(
% 1.63/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.63/0.65    inference(avatar_component_clause,[],[f114])).
% 1.63/0.65  fof(f372,plain,(
% 1.63/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(subsumption_resolution,[],[f371,f141])).
% 1.63/0.65  fof(f141,plain,(
% 1.63/0.65    v1_funct_1(sK2) | ~spl4_12),
% 1.63/0.65    inference(avatar_component_clause,[],[f139])).
% 1.63/0.65  fof(f371,plain,(
% 1.63/0.65    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(subsumption_resolution,[],[f370,f131])).
% 1.63/0.65  fof(f131,plain,(
% 1.63/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.63/0.65    inference(avatar_component_clause,[],[f129])).
% 1.63/0.65  fof(f370,plain,(
% 1.63/0.65    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(duplicate_literal_removal,[],[f369])).
% 1.63/0.65  fof(f369,plain,(
% 1.63/0.65    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(superposition,[],[f363,f73])).
% 1.63/0.65  fof(f73,plain,(
% 1.63/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f36])).
% 1.63/0.65  fof(f36,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.63/0.65    inference(flattening,[],[f35])).
% 1.63/0.65  fof(f35,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.63/0.65    inference(ennf_transformation,[],[f11])).
% 1.63/0.65  fof(f11,axiom,(
% 1.63/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.63/0.65  fof(f363,plain,(
% 1.63/0.65    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(subsumption_resolution,[],[f362,f141])).
% 1.63/0.65  fof(f362,plain,(
% 1.63/0.65    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.63/0.65    inference(subsumption_resolution,[],[f361,f136])).
% 1.63/0.65  fof(f136,plain,(
% 1.63/0.65    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.63/0.65    inference(avatar_component_clause,[],[f134])).
% 1.63/0.65  fof(f361,plain,(
% 1.63/0.65    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.63/0.65    inference(subsumption_resolution,[],[f360,f131])).
% 1.63/0.65  fof(f360,plain,(
% 1.63/0.65    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.63/0.65    inference(trivial_inequality_removal,[],[f355])).
% 1.63/0.65  fof(f355,plain,(
% 1.63/0.65    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.63/0.65    inference(superposition,[],[f62,f111])).
% 1.63/0.65  fof(f111,plain,(
% 1.63/0.65    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.63/0.65    inference(avatar_component_clause,[],[f109])).
% 1.63/0.65  fof(f62,plain,(
% 1.63/0.65    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f28])).
% 1.63/0.65  fof(f28,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.63/0.65    inference(flattening,[],[f27])).
% 1.63/0.65  fof(f27,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.63/0.65    inference(ennf_transformation,[],[f14])).
% 1.63/0.65  fof(f14,axiom,(
% 1.63/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.63/0.65  fof(f484,plain,(
% 1.63/0.65    ~spl4_31 | spl4_42 | ~spl4_43 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_30 | ~spl4_39),
% 1.63/0.65    inference(avatar_split_clause,[],[f475,f403,f320,f182,f161,f155,f139,f124,f481,f477,f328])).
% 1.63/0.65  fof(f477,plain,(
% 1.63/0.65    spl4_42 <=> sK2 = k2_funct_1(sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.63/0.65  fof(f161,plain,(
% 1.63/0.65    spl4_15 <=> v1_relat_1(sK2)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.63/0.65  fof(f182,plain,(
% 1.63/0.65    spl4_18 <=> sK1 = k2_relat_1(sK2)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.63/0.65  fof(f475,plain,(
% 1.63/0.65    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_18 | ~spl4_30 | ~spl4_39)),
% 1.63/0.65    inference(forward_demodulation,[],[f474,f184])).
% 1.63/0.65  fof(f184,plain,(
% 1.63/0.65    sK1 = k2_relat_1(sK2) | ~spl4_18),
% 1.63/0.65    inference(avatar_component_clause,[],[f182])).
% 1.63/0.65  fof(f474,plain,(
% 1.63/0.65    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_30 | ~spl4_39)),
% 1.63/0.65    inference(trivial_inequality_removal,[],[f473])).
% 1.63/0.65  fof(f473,plain,(
% 1.63/0.65    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_30 | ~spl4_39)),
% 1.63/0.65    inference(forward_demodulation,[],[f472,f322])).
% 1.63/0.65  fof(f472,plain,(
% 1.63/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_39)),
% 1.63/0.65    inference(subsumption_resolution,[],[f471,f157])).
% 1.63/0.65  fof(f471,plain,(
% 1.63/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_39)),
% 1.63/0.65    inference(subsumption_resolution,[],[f470,f126])).
% 1.63/0.65  fof(f470,plain,(
% 1.63/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_39)),
% 1.63/0.65    inference(subsumption_resolution,[],[f469,f163])).
% 1.63/0.65  fof(f163,plain,(
% 1.63/0.65    v1_relat_1(sK2) | ~spl4_15),
% 1.63/0.65    inference(avatar_component_clause,[],[f161])).
% 1.63/0.65  fof(f469,plain,(
% 1.63/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_39)),
% 1.63/0.65    inference(subsumption_resolution,[],[f464,f141])).
% 1.63/0.65  fof(f464,plain,(
% 1.63/0.65    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_39),
% 1.63/0.65    inference(superposition,[],[f57,f405])).
% 1.63/0.65  fof(f449,plain,(
% 1.63/0.65    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_38),
% 1.63/0.65    inference(avatar_contradiction_clause,[],[f447])).
% 1.63/0.65  fof(f447,plain,(
% 1.63/0.65    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_38)),
% 1.63/0.65    inference(unit_resulting_resolution,[],[f141,f126,f131,f116,f401,f207])).
% 1.63/0.65  fof(f207,plain,(
% 1.63/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.63/0.65    inference(duplicate_literal_removal,[],[f206])).
% 1.63/0.65  fof(f206,plain,(
% 1.63/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.63/0.65    inference(superposition,[],[f72,f73])).
% 1.63/0.65  fof(f72,plain,(
% 1.63/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f34])).
% 1.63/0.65  fof(f34,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.63/0.65    inference(flattening,[],[f33])).
% 1.63/0.65  fof(f33,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.63/0.65    inference(ennf_transformation,[],[f9])).
% 1.63/0.65  fof(f9,axiom,(
% 1.63/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.63/0.65  fof(f401,plain,(
% 1.63/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_38),
% 1.63/0.65    inference(avatar_component_clause,[],[f399])).
% 1.63/0.65  fof(f399,plain,(
% 1.63/0.65    spl4_38 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.63/0.65  fof(f406,plain,(
% 1.63/0.65    ~spl4_38 | spl4_39 | ~spl4_19),
% 1.63/0.65    inference(avatar_split_clause,[],[f387,f199,f403,f399])).
% 1.63/0.65  fof(f199,plain,(
% 1.63/0.65    spl4_19 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.63/0.65  fof(f387,plain,(
% 1.63/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_19),
% 1.63/0.65    inference(resolution,[],[f190,f201])).
% 1.63/0.65  fof(f201,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_19),
% 1.63/0.65    inference(avatar_component_clause,[],[f199])).
% 1.63/0.65  fof(f190,plain,(
% 1.63/0.65    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.63/0.65    inference(resolution,[],[f66,f149])).
% 1.63/0.65  fof(f149,plain,(
% 1.63/0.65    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.63/0.65    inference(forward_demodulation,[],[f69,f70])).
% 1.63/0.65  fof(f70,plain,(
% 1.63/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f12])).
% 1.63/0.65  fof(f12,axiom,(
% 1.63/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.63/0.65  fof(f69,plain,(
% 1.63/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.63/0.65    inference(cnf_transformation,[],[f18])).
% 1.63/0.65  fof(f18,plain,(
% 1.63/0.65    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.63/0.65    inference(pure_predicate_removal,[],[f10])).
% 1.63/0.65  fof(f10,axiom,(
% 1.63/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.63/0.65  fof(f66,plain,(
% 1.63/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.65    inference(cnf_transformation,[],[f42])).
% 1.63/0.65  fof(f42,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.65    inference(nnf_transformation,[],[f30])).
% 1.63/0.65  fof(f30,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.65    inference(flattening,[],[f29])).
% 1.63/0.65  fof(f29,plain,(
% 1.63/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.63/0.65    inference(ennf_transformation,[],[f8])).
% 1.63/0.65  fof(f8,axiom,(
% 1.63/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.63/0.65  fof(f354,plain,(
% 1.63/0.65    spl4_30 | ~spl4_7 | ~spl4_29),
% 1.63/0.65    inference(avatar_split_clause,[],[f353,f302,f114,f320])).
% 1.63/0.65  fof(f302,plain,(
% 1.63/0.65    spl4_29 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.63/0.65  fof(f353,plain,(
% 1.63/0.65    sK0 = k2_relat_1(sK3) | (~spl4_7 | ~spl4_29)),
% 1.63/0.65    inference(subsumption_resolution,[],[f314,f116])).
% 1.63/0.65  fof(f314,plain,(
% 1.63/0.65    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_29),
% 1.63/0.65    inference(superposition,[],[f74,f304])).
% 1.63/0.65  fof(f304,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_29),
% 1.63/0.65    inference(avatar_component_clause,[],[f302])).
% 1.63/0.65  fof(f74,plain,(
% 1.63/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.65    inference(cnf_transformation,[],[f37])).
% 1.63/0.65  fof(f37,plain,(
% 1.63/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.65    inference(ennf_transformation,[],[f7])).
% 1.63/0.65  fof(f7,axiom,(
% 1.63/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.63/0.65  fof(f352,plain,(
% 1.63/0.65    spl4_34 | ~spl4_31 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_29),
% 1.63/0.65    inference(avatar_split_clause,[],[f347,f302,f124,f119,f114,f94,f328,f349])).
% 1.63/0.65  fof(f347,plain,(
% 1.63/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_29)),
% 1.63/0.65    inference(subsumption_resolution,[],[f346,f126])).
% 1.63/0.65  fof(f346,plain,(
% 1.63/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_29)),
% 1.63/0.65    inference(subsumption_resolution,[],[f345,f121])).
% 1.63/0.65  fof(f345,plain,(
% 1.63/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_29)),
% 1.63/0.65    inference(subsumption_resolution,[],[f344,f116])).
% 1.63/0.65  fof(f344,plain,(
% 1.63/0.65    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_29)),
% 1.63/0.65    inference(subsumption_resolution,[],[f315,f96])).
% 1.63/0.65  fof(f315,plain,(
% 1.63/0.65    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_29),
% 1.63/0.65    inference(trivial_inequality_removal,[],[f313])).
% 1.63/0.65  fof(f313,plain,(
% 1.63/0.65    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_29),
% 1.63/0.65    inference(superposition,[],[f209,f304])).
% 1.63/0.65  fof(f209,plain,(
% 1.63/0.65    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.65    inference(forward_demodulation,[],[f55,f70])).
% 1.63/0.65  fof(f55,plain,(
% 1.63/0.65    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f22])).
% 1.63/0.65  fof(f22,plain,(
% 1.63/0.65    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.63/0.65    inference(flattening,[],[f21])).
% 1.63/0.65  fof(f21,plain,(
% 1.63/0.65    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.63/0.65    inference(ennf_transformation,[],[f15])).
% 1.63/0.65  fof(f15,axiom,(
% 1.63/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.63/0.65  fof(f305,plain,(
% 1.63/0.65    spl4_29 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.63/0.65    inference(avatar_split_clause,[],[f300,f145,f139,f134,f129,f124,f119,f114,f302])).
% 1.63/0.65  fof(f145,plain,(
% 1.63/0.65    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.63/0.65  fof(f300,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f299,f126])).
% 1.63/0.65  fof(f299,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f298,f121])).
% 1.63/0.65  fof(f298,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f297,f116])).
% 1.63/0.65  fof(f297,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f296,f141])).
% 1.63/0.65  fof(f296,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f295,f136])).
% 1.63/0.65  fof(f295,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f292,f131])).
% 1.63/0.65  fof(f292,plain,(
% 1.63/0.65    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 1.63/0.65    inference(resolution,[],[f290,f147])).
% 1.63/0.65  fof(f147,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.63/0.65    inference(avatar_component_clause,[],[f145])).
% 1.63/0.65  fof(f290,plain,(
% 1.63/0.65    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.65    inference(forward_demodulation,[],[f68,f70])).
% 1.63/0.65  fof(f68,plain,(
% 1.63/0.65    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f32])).
% 1.63/0.65  fof(f32,plain,(
% 1.63/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.63/0.65    inference(flattening,[],[f31])).
% 1.63/0.65  fof(f31,plain,(
% 1.63/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.63/0.65    inference(ennf_transformation,[],[f13])).
% 1.63/0.65  fof(f13,axiom,(
% 1.63/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.63/0.65  fof(f243,plain,(
% 1.63/0.65    spl4_21 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_20),
% 1.63/0.65    inference(avatar_split_clause,[],[f242,f223,f161,f139,f99,f235])).
% 1.63/0.65  fof(f235,plain,(
% 1.63/0.65    spl4_21 <=> sK0 = k1_relat_1(sK2)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.63/0.65  fof(f99,plain,(
% 1.63/0.65    spl4_4 <=> v2_funct_1(sK2)),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.63/0.65  fof(f223,plain,(
% 1.63/0.65    spl4_20 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.63/0.65  fof(f242,plain,(
% 1.63/0.65    sK0 = k1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_20)),
% 1.63/0.65    inference(forward_demodulation,[],[f241,f75])).
% 1.63/0.65  fof(f75,plain,(
% 1.63/0.65    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.63/0.65    inference(cnf_transformation,[],[f3])).
% 1.63/0.65  fof(f241,plain,(
% 1.63/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_20)),
% 1.63/0.65    inference(subsumption_resolution,[],[f240,f163])).
% 1.63/0.65  fof(f240,plain,(
% 1.63/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_20)),
% 1.63/0.65    inference(subsumption_resolution,[],[f239,f141])).
% 1.63/0.65  fof(f239,plain,(
% 1.63/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_20)),
% 1.63/0.65    inference(subsumption_resolution,[],[f228,f101])).
% 1.63/0.65  fof(f101,plain,(
% 1.63/0.65    v2_funct_1(sK2) | ~spl4_4),
% 1.63/0.65    inference(avatar_component_clause,[],[f99])).
% 1.63/0.65  fof(f228,plain,(
% 1.63/0.65    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_20),
% 1.63/0.65    inference(superposition,[],[f58,f225])).
% 1.63/0.65  fof(f225,plain,(
% 1.63/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_20),
% 1.63/0.65    inference(avatar_component_clause,[],[f223])).
% 1.63/0.65  fof(f58,plain,(
% 1.63/0.65    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f26])).
% 1.63/0.65  fof(f226,plain,(
% 1.63/0.65    spl4_20 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.63/0.65    inference(avatar_split_clause,[],[f221,f139,f134,f129,f109,f99,f89,f223])).
% 1.63/0.65  fof(f89,plain,(
% 1.63/0.65    spl4_2 <=> k1_xboole_0 = sK1),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.63/0.65  fof(f221,plain,(
% 1.63/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.63/0.65    inference(subsumption_resolution,[],[f220,f141])).
% 1.63/0.65  fof(f220,plain,(
% 1.63/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.63/0.65    inference(subsumption_resolution,[],[f219,f136])).
% 1.63/0.65  fof(f219,plain,(
% 1.63/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.63/0.65    inference(subsumption_resolution,[],[f218,f131])).
% 1.63/0.65  fof(f218,plain,(
% 1.63/0.65    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.63/0.65    inference(subsumption_resolution,[],[f217,f101])).
% 1.63/0.65  fof(f217,plain,(
% 1.63/0.65    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.63/0.65    inference(subsumption_resolution,[],[f216,f91])).
% 1.63/0.65  fof(f91,plain,(
% 1.63/0.65    k1_xboole_0 != sK1 | spl4_2),
% 1.63/0.65    inference(avatar_component_clause,[],[f89])).
% 1.63/0.65  fof(f216,plain,(
% 1.63/0.65    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.63/0.65    inference(trivial_inequality_removal,[],[f213])).
% 1.63/0.65  fof(f213,plain,(
% 1.63/0.65    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.63/0.65    inference(superposition,[],[f209,f111])).
% 1.63/0.65  fof(f202,plain,(
% 1.63/0.65    spl4_19 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.63/0.65    inference(avatar_split_clause,[],[f197,f145,f139,f129,f124,f114,f199])).
% 1.63/0.65  fof(f197,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f196,f141])).
% 1.63/0.65  fof(f196,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f195,f131])).
% 1.63/0.65  fof(f195,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f194,f126])).
% 1.63/0.65  fof(f194,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.63/0.65    inference(subsumption_resolution,[],[f191,f116])).
% 1.63/0.65  fof(f191,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.63/0.65    inference(superposition,[],[f147,f73])).
% 1.63/0.65  fof(f187,plain,(
% 1.63/0.65    spl4_18 | ~spl4_6 | ~spl4_10),
% 1.63/0.65    inference(avatar_split_clause,[],[f186,f129,f109,f182])).
% 1.63/0.65  fof(f186,plain,(
% 1.63/0.65    sK1 = k2_relat_1(sK2) | (~spl4_6 | ~spl4_10)),
% 1.63/0.65    inference(subsumption_resolution,[],[f179,f131])).
% 1.63/0.65  fof(f179,plain,(
% 1.63/0.65    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 1.63/0.65    inference(superposition,[],[f111,f74])).
% 1.63/0.65  fof(f164,plain,(
% 1.63/0.65    spl4_15 | ~spl4_10),
% 1.63/0.65    inference(avatar_split_clause,[],[f159,f129,f161])).
% 1.63/0.65  fof(f159,plain,(
% 1.63/0.65    v1_relat_1(sK2) | ~spl4_10),
% 1.63/0.65    inference(subsumption_resolution,[],[f151,f78])).
% 1.63/0.65  fof(f78,plain,(
% 1.63/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.63/0.65    inference(cnf_transformation,[],[f2])).
% 1.63/0.65  fof(f2,axiom,(
% 1.63/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.63/0.65  fof(f151,plain,(
% 1.63/0.65    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 1.63/0.65    inference(resolution,[],[f77,f131])).
% 1.63/0.65  fof(f77,plain,(
% 1.63/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.63/0.65    inference(cnf_transformation,[],[f38])).
% 1.63/0.65  fof(f38,plain,(
% 1.63/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.63/0.65    inference(ennf_transformation,[],[f1])).
% 1.63/0.65  fof(f1,axiom,(
% 1.63/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.63/0.65  fof(f158,plain,(
% 1.63/0.65    spl4_14 | ~spl4_7),
% 1.63/0.65    inference(avatar_split_clause,[],[f153,f114,f155])).
% 1.63/0.65  fof(f153,plain,(
% 1.63/0.65    v1_relat_1(sK3) | ~spl4_7),
% 1.63/0.65    inference(subsumption_resolution,[],[f150,f78])).
% 1.63/0.65  fof(f150,plain,(
% 1.63/0.65    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 1.63/0.65    inference(resolution,[],[f77,f116])).
% 1.63/0.65  fof(f148,plain,(
% 1.63/0.65    spl4_13 | ~spl4_5),
% 1.63/0.65    inference(avatar_split_clause,[],[f143,f104,f145])).
% 1.63/0.65  fof(f104,plain,(
% 1.63/0.65    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.63/0.65  fof(f143,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.63/0.65    inference(backward_demodulation,[],[f106,f70])).
% 1.63/0.65  fof(f106,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.63/0.65    inference(avatar_component_clause,[],[f104])).
% 1.63/0.65  fof(f142,plain,(
% 1.63/0.65    spl4_12),
% 1.63/0.65    inference(avatar_split_clause,[],[f43,f139])).
% 1.63/0.65  fof(f43,plain,(
% 1.63/0.65    v1_funct_1(sK2)),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f41,plain,(
% 1.63/0.65    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.63/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f40,f39])).
% 1.63/0.65  fof(f39,plain,(
% 1.63/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.63/0.65    introduced(choice_axiom,[])).
% 1.63/0.65  fof(f40,plain,(
% 1.63/0.65    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.63/0.65    introduced(choice_axiom,[])).
% 1.63/0.65  fof(f20,plain,(
% 1.63/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.63/0.65    inference(flattening,[],[f19])).
% 1.63/0.65  fof(f19,plain,(
% 1.63/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.63/0.65    inference(ennf_transformation,[],[f17])).
% 1.63/0.65  fof(f17,negated_conjecture,(
% 1.63/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.63/0.65    inference(negated_conjecture,[],[f16])).
% 1.63/0.65  fof(f16,conjecture,(
% 1.63/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.63/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.63/0.65  fof(f137,plain,(
% 1.63/0.65    spl4_11),
% 1.63/0.65    inference(avatar_split_clause,[],[f44,f134])).
% 1.63/0.65  fof(f44,plain,(
% 1.63/0.65    v1_funct_2(sK2,sK0,sK1)),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f132,plain,(
% 1.63/0.65    spl4_10),
% 1.63/0.65    inference(avatar_split_clause,[],[f45,f129])).
% 1.63/0.65  fof(f45,plain,(
% 1.63/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f127,plain,(
% 1.63/0.65    spl4_9),
% 1.63/0.65    inference(avatar_split_clause,[],[f46,f124])).
% 1.63/0.65  fof(f46,plain,(
% 1.63/0.65    v1_funct_1(sK3)),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f122,plain,(
% 1.63/0.65    spl4_8),
% 1.63/0.65    inference(avatar_split_clause,[],[f47,f119])).
% 1.63/0.65  fof(f47,plain,(
% 1.63/0.65    v1_funct_2(sK3,sK1,sK0)),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f117,plain,(
% 1.63/0.65    spl4_7),
% 1.63/0.65    inference(avatar_split_clause,[],[f48,f114])).
% 1.63/0.65  fof(f48,plain,(
% 1.63/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f112,plain,(
% 1.63/0.65    spl4_6),
% 1.63/0.65    inference(avatar_split_clause,[],[f49,f109])).
% 1.63/0.65  fof(f49,plain,(
% 1.63/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f107,plain,(
% 1.63/0.65    spl4_5),
% 1.63/0.65    inference(avatar_split_clause,[],[f50,f104])).
% 1.63/0.65  fof(f50,plain,(
% 1.63/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f102,plain,(
% 1.63/0.65    spl4_4),
% 1.63/0.65    inference(avatar_split_clause,[],[f51,f99])).
% 1.63/0.65  fof(f51,plain,(
% 1.63/0.65    v2_funct_1(sK2)),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f97,plain,(
% 1.63/0.65    ~spl4_3),
% 1.63/0.65    inference(avatar_split_clause,[],[f52,f94])).
% 1.63/0.65  fof(f52,plain,(
% 1.63/0.65    k1_xboole_0 != sK0),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f92,plain,(
% 1.63/0.65    ~spl4_2),
% 1.63/0.65    inference(avatar_split_clause,[],[f53,f89])).
% 1.63/0.65  fof(f53,plain,(
% 1.63/0.65    k1_xboole_0 != sK1),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  fof(f87,plain,(
% 1.63/0.65    ~spl4_1),
% 1.63/0.65    inference(avatar_split_clause,[],[f54,f84])).
% 1.63/0.65  fof(f84,plain,(
% 1.63/0.65    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.63/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.63/0.65  fof(f54,plain,(
% 1.63/0.65    k2_funct_1(sK2) != sK3),
% 1.63/0.65    inference(cnf_transformation,[],[f41])).
% 1.63/0.65  % SZS output end Proof for theBenchmark
% 1.63/0.65  % (31709)------------------------------
% 1.63/0.65  % (31709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.65  % (31709)Termination reason: Refutation
% 1.63/0.65  
% 1.63/0.65  % (31709)Memory used [KB]: 6652
% 1.63/0.65  % (31709)Time elapsed: 0.208 s
% 1.63/0.65  % (31709)------------------------------
% 1.63/0.65  % (31709)------------------------------
% 1.63/0.66  % (31687)Success in time 0.298 s
%------------------------------------------------------------------------------
