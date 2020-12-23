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
% DateTime   : Thu Dec  3 13:02:45 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  312 ( 731 expanded)
%              Number of leaves         :   67 ( 323 expanded)
%              Depth                    :   15
%              Number of atoms          : 1467 (3433 expanded)
%              Number of equality atoms :  288 ( 870 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f147,f155,f160,f202,f223,f238,f277,f289,f307,f325,f353,f362,f387,f415,f439,f448,f525,f546,f621,f847,f865,f871,f886,f919,f981,f1029,f1107,f1109,f1110,f1111,f1112,f1113,f1119])).

fof(f1119,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1113,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | sK0 != k1_relat_1(sK2)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1112,plain,
    ( sK2 != k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1111,plain,
    ( sK2 != k2_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1110,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1109,plain,
    ( sK2 != k2_funct_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1107,plain,
    ( spl4_74
    | ~ spl4_78 ),
    inference(avatar_contradiction_clause,[],[f1106])).

fof(f1106,plain,
    ( $false
    | spl4_74
    | ~ spl4_78 ),
    inference(subsumption_resolution,[],[f1105,f864])).

fof(f864,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_74 ),
    inference(avatar_component_clause,[],[f862])).

fof(f862,plain,
    ( spl4_74
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1105,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_78 ),
    inference(forward_demodulation,[],[f1085,f75])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1085,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_78 ),
    inference(superposition,[],[f75,f914])).

fof(f914,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f912])).

fof(f912,plain,
    ( spl4_78
  <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f1029,plain,
    ( spl4_95
    | ~ spl4_73 ),
    inference(avatar_split_clause,[],[f1028,f858,f1024])).

fof(f1024,plain,
    ( spl4_95
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f858,plain,
    ( spl4_73
  <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1028,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_73 ),
    inference(forward_demodulation,[],[f1000,f75])).

fof(f1000,plain,
    ( k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3)
    | ~ spl4_73 ),
    inference(superposition,[],[f75,f859])).

fof(f859,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f858])).

fof(f981,plain,
    ( ~ spl4_88
    | ~ spl4_75
    | ~ spl4_89
    | ~ spl4_90
    | spl4_91
    | ~ spl4_92
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f960,f359,f152,f123,f978,f974,f970,f966,f889,f962])).

fof(f962,plain,
    ( spl4_88
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f889,plain,
    ( spl4_75
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f966,plain,
    ( spl4_89
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f970,plain,
    ( spl4_90
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f974,plain,
    ( spl4_91
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).

fof(f978,plain,
    ( spl4_92
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f123,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f152,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f359,plain,
    ( spl4_36
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f960,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f959,f154])).

fof(f154,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f959,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f907,f125])).

fof(f125,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f907,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_36 ),
    inference(superposition,[],[f57,f361])).

fof(f361,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f359])).

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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f919,plain,
    ( spl4_78
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_33
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f918,f359,f338,f152,f123,f912])).

fof(f338,plain,
    ( spl4_33
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f918,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_33
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f917,f154])).

fof(f917,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_33
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f916,f125])).

fof(f916,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f902,f340])).

fof(f340,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f338])).

fof(f902,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_36 ),
    inference(superposition,[],[f58,f361])).

fof(f58,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f886,plain,
    ( spl4_73
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_33
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f885,f350,f338,f152,f123,f858])).

fof(f350,plain,
    ( spl4_35
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f885,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_33
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f884,f154])).

fof(f884,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_33
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f883,f125])).

fof(f883,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f873,f340])).

fof(f873,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_35 ),
    inference(superposition,[],[f59,f352])).

fof(f352,plain,
    ( k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f350])).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f871,plain,
    ( spl4_50
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_28
    | ~ spl4_31
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f870,f458,f302,f286,f157,f138,f98,f607])).

fof(f607,plain,
    ( spl4_50
  <=> v2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f98,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f138,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f157,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f286,plain,
    ( spl4_28
  <=> sK2 = k5_relat_1(k6_relat_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f302,plain,
    ( spl4_31
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f458,plain,
    ( spl4_45
  <=> v1_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f870,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_28
    | ~ spl4_31
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f869,f100])).

fof(f100,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f869,plain,
    ( ~ v2_funct_1(sK2)
    | v2_funct_1(k6_relat_1(sK0))
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_28
    | ~ spl4_31
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f868,f288])).

fof(f288,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f286])).

fof(f868,plain,
    ( ~ v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2))
    | v2_funct_1(k6_relat_1(sK0))
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_31
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f867,f159])).

fof(f159,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f867,plain,
    ( ~ v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2))
    | v2_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_31
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f866,f140])).

fof(f140,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f866,plain,
    ( ~ v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2))
    | v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_31
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f825,f459])).

fof(f459,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f458])).

fof(f825,plain,
    ( ~ v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2))
    | v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_31 ),
    inference(superposition,[],[f505,f304])).

fof(f304,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f302])).

fof(f505,plain,(
    ! [X0] :
      ( ~ v2_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0))
      | v2_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(k1_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f501])).

fof(f501,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != X0
      | v2_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f176,f150])).

fof(f150,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(resolution,[],[f76,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f176,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != X0
      | v2_funct_1(k6_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f64,f75])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
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
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f865,plain,
    ( ~ spl4_33
    | spl4_72
    | ~ spl4_73
    | ~ spl4_74
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f852,f445,f410,f157,f152,f138,f123,f862,f858,f854,f338])).

fof(f854,plain,
    ( spl4_72
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f410,plain,
    ( spl4_40
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f445,plain,
    ( spl4_44
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f852,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_40
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f851,f412])).

fof(f412,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f410])).

fof(f851,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f850,f154])).

fof(f850,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f849,f125])).

fof(f849,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f848,f159])).

fof(f848,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_12
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f567,f140])).

fof(f567,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_44 ),
    inference(superposition,[],[f57,f447])).

fof(f447,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f445])).

fof(f847,plain,
    ( spl4_33
    | ~ spl4_50
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f846,f436,f138,f133,f128,f123,f118,f113,f108,f93,f607,f338])).

fof(f93,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f108,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f113,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f118,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f128,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f133,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f436,plain,
    ( spl4_42
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f846,plain,
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
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f845,f125])).

fof(f845,plain,
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
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f844,f120])).

fof(f120,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f844,plain,
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
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f843,f115])).

fof(f115,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f843,plain,
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
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f593,f95])).

fof(f95,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f593,plain,
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
    | ~ spl4_42 ),
    inference(superposition,[],[f369,f438])).

fof(f438,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f436])).

fof(f369,plain,
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
    inference(subsumption_resolution,[],[f368,f140])).

fof(f368,plain,
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
    inference(subsumption_resolution,[],[f367,f135])).

fof(f135,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f367,plain,
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
    inference(subsumption_resolution,[],[f366,f130])).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f366,plain,
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
    inference(trivial_inequality_removal,[],[f363])).

fof(f363,plain,
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
    inference(superposition,[],[f62,f110])).

fof(f110,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f108])).

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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f621,plain,
    ( spl4_45
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f620,f436,f138,f128,f123,f113,f458])).

fof(f620,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f619,f140])).

fof(f619,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f618,f130])).

fof(f618,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f617,f125])).

fof(f617,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f599,f115])).

fof(f599,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_42 ),
    inference(superposition,[],[f70,f438])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
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

fof(f546,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_43 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_43 ),
    inference(unit_resulting_resolution,[],[f140,f125,f130,f115,f443,f209])).

fof(f209,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
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
    inference(superposition,[],[f71,f72])).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f443,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl4_43
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f525,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_41 ),
    inference(subsumption_resolution,[],[f523,f140])).

fof(f523,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_41 ),
    inference(subsumption_resolution,[],[f522,f130])).

fof(f522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_41 ),
    inference(subsumption_resolution,[],[f521,f125])).

fof(f521,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_41 ),
    inference(subsumption_resolution,[],[f518,f115])).

fof(f518,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_41 ),
    inference(resolution,[],[f434,f71])).

fof(f434,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl4_41
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f448,plain,
    ( ~ spl4_43
    | spl4_44
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f429,f199,f445,f441])).

fof(f199,plain,
    ( spl4_18
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f429,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_18 ),
    inference(resolution,[],[f181,f201])).

fof(f201,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f181,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f66,f77])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f439,plain,
    ( ~ spl4_41
    | spl4_42
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f428,f144,f436,f432])).

fof(f144,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f428,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f181,f146])).

fof(f146,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f415,plain,
    ( spl4_40
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f414,f380,f410])).

fof(f380,plain,
    ( spl4_37
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f414,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f397,f74])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f397,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1))
    | ~ spl4_37 ),
    inference(superposition,[],[f74,f382])).

fof(f382,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f380])).

fof(f387,plain,
    ( spl4_37
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f386,f274,f157,f138,f98,f380])).

fof(f274,plain,
    ( spl4_27
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f386,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f385,f159])).

fof(f385,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f384,f140])).

fof(f384,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f374,f100])).

fof(f374,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_27 ),
    inference(superposition,[],[f59,f276])).

fof(f276,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f274])).

fof(f362,plain,
    ( spl4_36
    | ~ spl4_33
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f357,f322,f123,f118,f113,f93,f338,f359])).

fof(f322,plain,
    ( spl4_32
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f357,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f356,f125])).

fof(f356,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f355,f120])).

fof(f355,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f354,f115])).

fof(f354,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f331,f95])).

fof(f331,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_32 ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_32 ),
    inference(superposition,[],[f210,f324])).

fof(f324,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f322])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f55,f69])).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f353,plain,
    ( spl4_35
    | ~ spl4_33
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f348,f322,f123,f118,f113,f93,f338,f350])).

fof(f348,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f347,f125])).

fof(f347,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f346,f120])).

fof(f346,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f345,f115])).

fof(f345,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f332,f95])).

fof(f332,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_32 ),
    inference(trivial_inequality_removal,[],[f329])).

fof(f329,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_32 ),
    inference(superposition,[],[f211,f324])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f56,f69])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f325,plain,
    ( spl4_32
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f320,f144,f138,f133,f128,f123,f118,f113,f322])).

fof(f320,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f319,f125])).

fof(f319,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f318,f120])).

fof(f318,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f317,f115])).

fof(f317,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f316,f140])).

fof(f316,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f315,f135])).

fof(f315,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f312,f130])).

fof(f312,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f308,f146])).

fof(f308,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f68,f69])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f307,plain,
    ( spl4_31
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f306,f231,f302])).

fof(f231,plain,
    ( spl4_20
  <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f306,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f283,f74])).

fof(f283,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ spl4_20 ),
    inference(superposition,[],[f74,f233])).

fof(f233,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f231])).

fof(f289,plain,
    ( spl4_28
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f284,f231,f157,f286])).

fof(f284,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f278,f159])).

fof(f278,plain,
    ( sK2 = k5_relat_1(k6_relat_1(sK0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(superposition,[],[f73,f233])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f277,plain,
    ( spl4_27
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f272,f138,f133,f128,f108,f98,f88,f274])).

fof(f88,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f272,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f271,f140])).

fof(f271,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f270,f135])).

fof(f270,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f269,f130])).

fof(f269,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f268,f100])).

fof(f268,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f267,f90])).

fof(f90,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f267,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f266])).

fof(f266,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f211,f110])).

fof(f238,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f237,f220,f157,f138,f98,f231])).

fof(f220,plain,
    ( spl4_19
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f237,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f236,f159])).

fof(f236,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f235,f140])).

fof(f235,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f225,f100])).

fof(f225,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(superposition,[],[f58,f222])).

fof(f222,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f220])).

fof(f223,plain,
    ( spl4_19
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f218,f138,f133,f128,f108,f98,f88,f220])).

fof(f218,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f217,f140])).

fof(f217,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f216,f135])).

fof(f216,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f215,f130])).

fof(f215,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f214,f100])).

fof(f214,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f213,f90])).

fof(f213,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f212])).

fof(f212,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f210,f110])).

fof(f202,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f197,f144,f138,f128,f123,f113,f199])).

fof(f197,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f196,f140])).

fof(f196,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f195,f130])).

fof(f195,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f194,f125])).

fof(f194,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f191,f115])).

fof(f191,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f146,f72])).

fof(f160,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f149,f128,f157])).

fof(f149,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(resolution,[],[f76,f130])).

fof(f155,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f148,f113,f152])).

fof(f148,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f76,f115])).

fof(f147,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f142,f103,f144])).

fof(f103,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f142,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f105,f69])).

fof(f105,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f141,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f43,f138])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f40,f39])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f136,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f44,f133])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f131,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f45,f128])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f126,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f46,f123])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f121,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f47,f118])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f48,f113])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f49,f108])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f98])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f52,f93])).

fof(f52,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f88])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f83])).

fof(f83,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f54,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:07:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.43  % (16389)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (16397)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.49  % (16392)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.49  % (16413)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (16384)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (16405)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (16404)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.50  % (16388)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (16396)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (16393)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (16383)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (16386)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (16400)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (16407)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (16398)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (16390)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (16402)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (16409)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (16403)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (16412)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (16387)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (16410)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.53  % (16411)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.53  % (16406)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.53  % (16399)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.54  % (16395)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.54  % (16382)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.54  % (16408)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.54  % (16394)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.54  % (16391)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.54/0.55  % (16399)Refutation not found, incomplete strategy% (16399)------------------------------
% 1.54/0.55  % (16399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (16399)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (16399)Memory used [KB]: 10746
% 1.54/0.56  % (16399)Time elapsed: 0.147 s
% 1.54/0.56  % (16399)------------------------------
% 1.54/0.56  % (16399)------------------------------
% 1.54/0.56  % (16405)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.57  % SZS output start Proof for theBenchmark
% 1.54/0.57  fof(f1120,plain,(
% 1.54/0.57    $false),
% 1.54/0.57    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f147,f155,f160,f202,f223,f238,f277,f289,f307,f325,f353,f362,f387,f415,f439,f448,f525,f546,f621,f847,f865,f871,f886,f919,f981,f1029,f1107,f1109,f1110,f1111,f1112,f1113,f1119])).
% 1.54/0.57  fof(f1119,plain,(
% 1.54/0.57    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | k2_funct_1(sK2) = sK3),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f1113,plain,(
% 1.54/0.57    sK2 != k2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | sK0 != k1_relat_1(sK2) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f1112,plain,(
% 1.54/0.57    sK2 != k2_funct_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(sK2)),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f1111,plain,(
% 1.54/0.57    sK2 != k2_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK2)),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f1110,plain,(
% 1.54/0.57    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f1109,plain,(
% 1.54/0.57    sK2 != k2_funct_1(sK3) | v1_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK2)),
% 1.54/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.57  fof(f1107,plain,(
% 1.54/0.57    spl4_74 | ~spl4_78),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f1106])).
% 1.54/0.57  fof(f1106,plain,(
% 1.54/0.57    $false | (spl4_74 | ~spl4_78)),
% 1.54/0.57    inference(subsumption_resolution,[],[f1105,f864])).
% 1.54/0.57  fof(f864,plain,(
% 1.54/0.57    sK1 != k1_relat_1(sK3) | spl4_74),
% 1.54/0.57    inference(avatar_component_clause,[],[f862])).
% 1.54/0.57  fof(f862,plain,(
% 1.54/0.57    spl4_74 <=> sK1 = k1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 1.54/0.57  fof(f1105,plain,(
% 1.54/0.57    sK1 = k1_relat_1(sK3) | ~spl4_78),
% 1.54/0.57    inference(forward_demodulation,[],[f1085,f75])).
% 1.54/0.57  fof(f75,plain,(
% 1.54/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.54/0.57  fof(f1085,plain,(
% 1.54/0.57    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~spl4_78),
% 1.54/0.57    inference(superposition,[],[f75,f914])).
% 1.54/0.57  fof(f914,plain,(
% 1.54/0.57    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~spl4_78),
% 1.54/0.57    inference(avatar_component_clause,[],[f912])).
% 1.54/0.57  fof(f912,plain,(
% 1.54/0.57    spl4_78 <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 1.54/0.57  fof(f1029,plain,(
% 1.54/0.57    spl4_95 | ~spl4_73),
% 1.54/0.57    inference(avatar_split_clause,[],[f1028,f858,f1024])).
% 1.54/0.57  fof(f1024,plain,(
% 1.54/0.57    spl4_95 <=> sK0 = k2_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).
% 1.54/0.57  fof(f858,plain,(
% 1.54/0.57    spl4_73 <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.54/0.57  fof(f1028,plain,(
% 1.54/0.57    sK0 = k2_relat_1(sK3) | ~spl4_73),
% 1.54/0.57    inference(forward_demodulation,[],[f1000,f75])).
% 1.54/0.57  fof(f1000,plain,(
% 1.54/0.57    k2_relat_1(k6_relat_1(sK0)) = k2_relat_1(sK3) | ~spl4_73),
% 1.54/0.57    inference(superposition,[],[f75,f859])).
% 1.54/0.57  fof(f859,plain,(
% 1.54/0.57    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~spl4_73),
% 1.54/0.57    inference(avatar_component_clause,[],[f858])).
% 1.54/0.57  fof(f981,plain,(
% 1.54/0.57    ~spl4_88 | ~spl4_75 | ~spl4_89 | ~spl4_90 | spl4_91 | ~spl4_92 | ~spl4_9 | ~spl4_14 | ~spl4_36),
% 1.54/0.57    inference(avatar_split_clause,[],[f960,f359,f152,f123,f978,f974,f970,f966,f889,f962])).
% 1.54/0.57  fof(f962,plain,(
% 1.54/0.57    spl4_88 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 1.54/0.57  fof(f889,plain,(
% 1.54/0.57    spl4_75 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.54/0.57  fof(f966,plain,(
% 1.54/0.57    spl4_89 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 1.54/0.57  fof(f970,plain,(
% 1.54/0.57    spl4_90 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 1.54/0.57  fof(f974,plain,(
% 1.54/0.57    spl4_91 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_91])])).
% 1.54/0.57  fof(f978,plain,(
% 1.54/0.57    spl4_92 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 1.54/0.57  fof(f123,plain,(
% 1.54/0.57    spl4_9 <=> v1_funct_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.54/0.57  fof(f152,plain,(
% 1.54/0.57    spl4_14 <=> v1_relat_1(sK3)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.54/0.57  fof(f359,plain,(
% 1.54/0.57    spl4_36 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.54/0.57  fof(f960,plain,(
% 1.54/0.57    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_36)),
% 1.54/0.57    inference(subsumption_resolution,[],[f959,f154])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    v1_relat_1(sK3) | ~spl4_14),
% 1.54/0.57    inference(avatar_component_clause,[],[f152])).
% 1.54/0.57  fof(f959,plain,(
% 1.54/0.57    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_36)),
% 1.54/0.57    inference(subsumption_resolution,[],[f907,f125])).
% 1.54/0.57  fof(f125,plain,(
% 1.54/0.57    v1_funct_1(sK3) | ~spl4_9),
% 1.54/0.57    inference(avatar_component_clause,[],[f123])).
% 1.54/0.57  fof(f907,plain,(
% 1.54/0.57    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_36),
% 1.54/0.57    inference(superposition,[],[f57,f361])).
% 1.54/0.57  fof(f361,plain,(
% 1.54/0.57    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_36),
% 1.54/0.57    inference(avatar_component_clause,[],[f359])).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f22])).
% 1.54/0.58  fof(f22,plain,(
% 1.54/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.58    inference(flattening,[],[f21])).
% 1.54/0.58  fof(f21,plain,(
% 1.54/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f5])).
% 1.54/0.58  fof(f5,axiom,(
% 1.54/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.54/0.58  fof(f919,plain,(
% 1.54/0.58    spl4_78 | ~spl4_9 | ~spl4_14 | ~spl4_33 | ~spl4_36),
% 1.54/0.58    inference(avatar_split_clause,[],[f918,f359,f338,f152,f123,f912])).
% 1.54/0.58  fof(f338,plain,(
% 1.54/0.58    spl4_33 <=> v2_funct_1(sK3)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.54/0.58  fof(f918,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_33 | ~spl4_36)),
% 1.54/0.58    inference(subsumption_resolution,[],[f917,f154])).
% 1.54/0.58  fof(f917,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_33 | ~spl4_36)),
% 1.54/0.58    inference(subsumption_resolution,[],[f916,f125])).
% 1.54/0.58  fof(f916,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_33 | ~spl4_36)),
% 1.54/0.58    inference(subsumption_resolution,[],[f902,f340])).
% 1.54/0.58  fof(f340,plain,(
% 1.54/0.58    v2_funct_1(sK3) | ~spl4_33),
% 1.54/0.58    inference(avatar_component_clause,[],[f338])).
% 1.54/0.58  fof(f902,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_36),
% 1.54/0.58    inference(superposition,[],[f58,f361])).
% 1.54/0.58  fof(f58,plain,(
% 1.54/0.58    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f24])).
% 1.54/0.58  fof(f24,plain,(
% 1.54/0.58    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.58    inference(flattening,[],[f23])).
% 1.54/0.58  fof(f23,plain,(
% 1.54/0.58    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.54/0.58  fof(f886,plain,(
% 1.54/0.58    spl4_73 | ~spl4_9 | ~spl4_14 | ~spl4_33 | ~spl4_35),
% 1.54/0.58    inference(avatar_split_clause,[],[f885,f350,f338,f152,f123,f858])).
% 1.54/0.58  fof(f350,plain,(
% 1.54/0.58    spl4_35 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.54/0.58  fof(f885,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_33 | ~spl4_35)),
% 1.54/0.58    inference(subsumption_resolution,[],[f884,f154])).
% 1.54/0.58  fof(f884,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_33 | ~spl4_35)),
% 1.54/0.58    inference(subsumption_resolution,[],[f883,f125])).
% 1.54/0.58  fof(f883,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_33 | ~spl4_35)),
% 1.54/0.58    inference(subsumption_resolution,[],[f873,f340])).
% 1.54/0.58  fof(f873,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_35),
% 1.54/0.58    inference(superposition,[],[f59,f352])).
% 1.54/0.58  fof(f352,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~spl4_35),
% 1.54/0.58    inference(avatar_component_clause,[],[f350])).
% 1.54/0.58  fof(f59,plain,(
% 1.54/0.58    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f24])).
% 1.54/0.58  fof(f871,plain,(
% 1.54/0.58    spl4_50 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_28 | ~spl4_31 | ~spl4_45),
% 1.54/0.58    inference(avatar_split_clause,[],[f870,f458,f302,f286,f157,f138,f98,f607])).
% 1.54/0.58  fof(f607,plain,(
% 1.54/0.58    spl4_50 <=> v2_funct_1(k6_relat_1(sK0))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.54/0.58  fof(f98,plain,(
% 1.54/0.58    spl4_4 <=> v2_funct_1(sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.54/0.58  fof(f138,plain,(
% 1.54/0.58    spl4_12 <=> v1_funct_1(sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.54/0.58  fof(f157,plain,(
% 1.54/0.58    spl4_15 <=> v1_relat_1(sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.54/0.58  fof(f286,plain,(
% 1.54/0.58    spl4_28 <=> sK2 = k5_relat_1(k6_relat_1(sK0),sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.54/0.58  fof(f302,plain,(
% 1.54/0.58    spl4_31 <=> sK0 = k1_relat_1(sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.54/0.58  fof(f458,plain,(
% 1.54/0.58    spl4_45 <=> v1_funct_1(k6_relat_1(sK0))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.54/0.58  fof(f870,plain,(
% 1.54/0.58    v2_funct_1(k6_relat_1(sK0)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_28 | ~spl4_31 | ~spl4_45)),
% 1.54/0.58    inference(subsumption_resolution,[],[f869,f100])).
% 1.54/0.58  fof(f100,plain,(
% 1.54/0.58    v2_funct_1(sK2) | ~spl4_4),
% 1.54/0.58    inference(avatar_component_clause,[],[f98])).
% 1.54/0.58  fof(f869,plain,(
% 1.54/0.58    ~v2_funct_1(sK2) | v2_funct_1(k6_relat_1(sK0)) | (~spl4_12 | ~spl4_15 | ~spl4_28 | ~spl4_31 | ~spl4_45)),
% 1.54/0.58    inference(forward_demodulation,[],[f868,f288])).
% 1.54/0.58  fof(f288,plain,(
% 1.54/0.58    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | ~spl4_28),
% 1.54/0.58    inference(avatar_component_clause,[],[f286])).
% 1.54/0.58  fof(f868,plain,(
% 1.54/0.58    ~v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2)) | v2_funct_1(k6_relat_1(sK0)) | (~spl4_12 | ~spl4_15 | ~spl4_31 | ~spl4_45)),
% 1.54/0.58    inference(subsumption_resolution,[],[f867,f159])).
% 1.54/0.58  fof(f159,plain,(
% 1.54/0.58    v1_relat_1(sK2) | ~spl4_15),
% 1.54/0.58    inference(avatar_component_clause,[],[f157])).
% 1.54/0.58  fof(f867,plain,(
% 1.54/0.58    ~v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2)) | v2_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | (~spl4_12 | ~spl4_31 | ~spl4_45)),
% 1.54/0.58    inference(subsumption_resolution,[],[f866,f140])).
% 1.54/0.58  fof(f140,plain,(
% 1.54/0.58    v1_funct_1(sK2) | ~spl4_12),
% 1.54/0.58    inference(avatar_component_clause,[],[f138])).
% 1.54/0.58  fof(f866,plain,(
% 1.54/0.58    ~v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2)) | v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_31 | ~spl4_45)),
% 1.54/0.58    inference(subsumption_resolution,[],[f825,f459])).
% 1.54/0.58  fof(f459,plain,(
% 1.54/0.58    v1_funct_1(k6_relat_1(sK0)) | ~spl4_45),
% 1.54/0.58    inference(avatar_component_clause,[],[f458])).
% 1.54/0.58  fof(f825,plain,(
% 1.54/0.58    ~v2_funct_1(k5_relat_1(k6_relat_1(sK0),sK2)) | v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_31),
% 1.54/0.58    inference(superposition,[],[f505,f304])).
% 1.54/0.58  fof(f304,plain,(
% 1.54/0.58    sK0 = k1_relat_1(sK2) | ~spl4_31),
% 1.54/0.58    inference(avatar_component_clause,[],[f302])).
% 1.54/0.58  fof(f505,plain,(
% 1.54/0.58    ( ! [X0] : (~v2_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0)) | v2_funct_1(k6_relat_1(k1_relat_1(X0))) | ~v1_funct_1(k6_relat_1(k1_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(equality_resolution,[],[f501])).
% 1.54/0.58  fof(f501,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_relat_1(X1) != X0 | v2_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f176,f150])).
% 1.54/0.58  fof(f150,plain,(
% 1.54/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.54/0.58    inference(resolution,[],[f76,f77])).
% 1.54/0.58  fof(f77,plain,(
% 1.54/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.54/0.58  fof(f76,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f38])).
% 1.54/0.58  fof(f38,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.58    inference(ennf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.54/0.58  fof(f176,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_relat_1(X1) != X0 | v2_funct_1(k6_relat_1(X0)) | ~v2_funct_1(k5_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.58    inference(superposition,[],[f64,f75])).
% 1.54/0.58  fof(f64,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f28])).
% 1.54/0.58  fof(f28,plain,(
% 1.54/0.58    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.58    inference(flattening,[],[f27])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f3])).
% 1.54/0.58  fof(f3,axiom,(
% 1.54/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.54/0.58  fof(f865,plain,(
% 1.54/0.58    ~spl4_33 | spl4_72 | ~spl4_73 | ~spl4_74 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_40 | ~spl4_44),
% 1.54/0.58    inference(avatar_split_clause,[],[f852,f445,f410,f157,f152,f138,f123,f862,f858,f854,f338])).
% 1.54/0.58  fof(f854,plain,(
% 1.54/0.58    spl4_72 <=> sK2 = k2_funct_1(sK3)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 1.54/0.58  fof(f410,plain,(
% 1.54/0.58    spl4_40 <=> sK1 = k2_relat_1(sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.54/0.58  fof(f445,plain,(
% 1.54/0.58    spl4_44 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.54/0.58  fof(f852,plain,(
% 1.54/0.58    sK1 != k1_relat_1(sK3) | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_40 | ~spl4_44)),
% 1.54/0.58    inference(forward_demodulation,[],[f851,f412])).
% 1.54/0.58  fof(f412,plain,(
% 1.54/0.58    sK1 = k2_relat_1(sK2) | ~spl4_40),
% 1.54/0.58    inference(avatar_component_clause,[],[f410])).
% 1.54/0.58  fof(f851,plain,(
% 1.54/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_44)),
% 1.54/0.58    inference(subsumption_resolution,[],[f850,f154])).
% 1.54/0.58  fof(f850,plain,(
% 1.54/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_12 | ~spl4_15 | ~spl4_44)),
% 1.54/0.58    inference(subsumption_resolution,[],[f849,f125])).
% 1.54/0.58  fof(f849,plain,(
% 1.54/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_15 | ~spl4_44)),
% 1.54/0.58    inference(subsumption_resolution,[],[f848,f159])).
% 1.54/0.58  fof(f848,plain,(
% 1.54/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_12 | ~spl4_44)),
% 1.54/0.58    inference(subsumption_resolution,[],[f567,f140])).
% 1.54/0.58  fof(f567,plain,(
% 1.54/0.58    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_44),
% 1.54/0.58    inference(superposition,[],[f57,f447])).
% 1.54/0.58  fof(f447,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_44),
% 1.54/0.58    inference(avatar_component_clause,[],[f445])).
% 1.54/0.58  fof(f847,plain,(
% 1.54/0.58    spl4_33 | ~spl4_50 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_42),
% 1.54/0.58    inference(avatar_split_clause,[],[f846,f436,f138,f133,f128,f123,f118,f113,f108,f93,f607,f338])).
% 1.54/0.58  fof(f93,plain,(
% 1.54/0.58    spl4_3 <=> k1_xboole_0 = sK0),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.54/0.58  fof(f108,plain,(
% 1.54/0.58    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.54/0.58  fof(f113,plain,(
% 1.54/0.58    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.54/0.58  fof(f118,plain,(
% 1.54/0.58    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.54/0.58  fof(f128,plain,(
% 1.54/0.58    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.54/0.58  fof(f133,plain,(
% 1.54/0.58    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.54/0.58  fof(f436,plain,(
% 1.54/0.58    spl4_42 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.54/0.58  fof(f846,plain,(
% 1.54/0.58    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f845,f125])).
% 1.54/0.58  fof(f845,plain,(
% 1.54/0.58    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f844,f120])).
% 1.54/0.58  fof(f120,plain,(
% 1.54/0.58    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 1.54/0.58    inference(avatar_component_clause,[],[f118])).
% 1.54/0.58  fof(f844,plain,(
% 1.54/0.58    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f843,f115])).
% 1.54/0.58  fof(f115,plain,(
% 1.54/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 1.54/0.58    inference(avatar_component_clause,[],[f113])).
% 1.54/0.58  fof(f843,plain,(
% 1.54/0.58    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f593,f95])).
% 1.54/0.58  fof(f95,plain,(
% 1.54/0.58    k1_xboole_0 != sK0 | spl4_3),
% 1.54/0.58    inference(avatar_component_clause,[],[f93])).
% 1.54/0.58  fof(f593,plain,(
% 1.54/0.58    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_42)),
% 1.54/0.58    inference(superposition,[],[f369,f438])).
% 1.54/0.58  fof(f438,plain,(
% 1.54/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_42),
% 1.54/0.58    inference(avatar_component_clause,[],[f436])).
% 1.54/0.58  fof(f369,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.54/0.58    inference(subsumption_resolution,[],[f368,f140])).
% 1.54/0.58  fof(f368,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.54/0.58    inference(subsumption_resolution,[],[f367,f135])).
% 1.54/0.58  fof(f135,plain,(
% 1.54/0.58    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 1.54/0.58    inference(avatar_component_clause,[],[f133])).
% 1.54/0.58  fof(f367,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 1.54/0.58    inference(subsumption_resolution,[],[f366,f130])).
% 1.54/0.58  fof(f130,plain,(
% 1.54/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 1.54/0.58    inference(avatar_component_clause,[],[f128])).
% 1.54/0.58  fof(f366,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f363])).
% 1.54/0.58  fof(f363,plain,(
% 1.54/0.58    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 1.54/0.58    inference(superposition,[],[f62,f110])).
% 1.54/0.58  fof(f110,plain,(
% 1.54/0.58    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 1.54/0.58    inference(avatar_component_clause,[],[f108])).
% 1.54/0.58  fof(f62,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f26])).
% 1.54/0.58  fof(f26,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.54/0.58    inference(flattening,[],[f25])).
% 1.54/0.58  fof(f25,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.54/0.58    inference(ennf_transformation,[],[f13])).
% 1.54/0.58  fof(f13,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.54/0.58  fof(f621,plain,(
% 1.54/0.58    spl4_45 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_42),
% 1.54/0.58    inference(avatar_split_clause,[],[f620,f436,f138,f128,f123,f113,f458])).
% 1.54/0.58  fof(f620,plain,(
% 1.54/0.58    v1_funct_1(k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f619,f140])).
% 1.54/0.58  fof(f619,plain,(
% 1.54/0.58    v1_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f618,f130])).
% 1.54/0.58  fof(f618,plain,(
% 1.54/0.58    v1_funct_1(k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f617,f125])).
% 1.54/0.58  fof(f617,plain,(
% 1.54/0.58    v1_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_42)),
% 1.54/0.58    inference(subsumption_resolution,[],[f599,f115])).
% 1.54/0.58  fof(f599,plain,(
% 1.54/0.58    v1_funct_1(k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_42),
% 1.54/0.58    inference(superposition,[],[f70,f438])).
% 1.54/0.58  fof(f70,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f34])).
% 1.54/0.58  fof(f34,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.58    inference(flattening,[],[f33])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.58    inference(ennf_transformation,[],[f9])).
% 1.54/0.58  fof(f9,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.54/0.58  fof(f546,plain,(
% 1.54/0.58    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_43),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f528])).
% 1.54/0.58  fof(f528,plain,(
% 1.54/0.58    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_43)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f140,f125,f130,f115,f443,f209])).
% 1.54/0.58  fof(f209,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.58    inference(duplicate_literal_removal,[],[f208])).
% 1.54/0.58  fof(f208,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.58    inference(superposition,[],[f71,f72])).
% 1.54/0.58  fof(f72,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f36])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.58    inference(flattening,[],[f35])).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.58    inference(ennf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.54/0.58  fof(f71,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f34])).
% 1.54/0.58  fof(f443,plain,(
% 1.54/0.58    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_43),
% 1.54/0.58    inference(avatar_component_clause,[],[f441])).
% 1.54/0.58  fof(f441,plain,(
% 1.54/0.58    spl4_43 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.54/0.58  fof(f525,plain,(
% 1.54/0.58    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_41),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f524])).
% 1.54/0.58  fof(f524,plain,(
% 1.54/0.58    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_41)),
% 1.54/0.58    inference(subsumption_resolution,[],[f523,f140])).
% 1.54/0.58  fof(f523,plain,(
% 1.54/0.58    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_41)),
% 1.54/0.58    inference(subsumption_resolution,[],[f522,f130])).
% 1.54/0.58  fof(f522,plain,(
% 1.54/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_41)),
% 1.54/0.58    inference(subsumption_resolution,[],[f521,f125])).
% 1.54/0.58  fof(f521,plain,(
% 1.54/0.58    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_41)),
% 1.54/0.58    inference(subsumption_resolution,[],[f518,f115])).
% 1.54/0.58  fof(f518,plain,(
% 1.54/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_41),
% 1.54/0.58    inference(resolution,[],[f434,f71])).
% 1.54/0.58  fof(f434,plain,(
% 1.54/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_41),
% 1.54/0.58    inference(avatar_component_clause,[],[f432])).
% 1.54/0.58  fof(f432,plain,(
% 1.54/0.58    spl4_41 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.54/0.58  fof(f448,plain,(
% 1.54/0.58    ~spl4_43 | spl4_44 | ~spl4_18),
% 1.54/0.58    inference(avatar_split_clause,[],[f429,f199,f445,f441])).
% 1.54/0.58  fof(f199,plain,(
% 1.54/0.58    spl4_18 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.54/0.58  fof(f429,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_18),
% 1.54/0.58    inference(resolution,[],[f181,f201])).
% 1.54/0.58  fof(f201,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_18),
% 1.54/0.58    inference(avatar_component_clause,[],[f199])).
% 1.54/0.58  fof(f181,plain,(
% 1.54/0.58    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.54/0.58    inference(resolution,[],[f66,f77])).
% 1.54/0.58  fof(f66,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f42])).
% 1.54/0.58  fof(f42,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.58    inference(nnf_transformation,[],[f30])).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.58    inference(flattening,[],[f29])).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.54/0.58    inference(ennf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.54/0.58  fof(f439,plain,(
% 1.54/0.58    ~spl4_41 | spl4_42 | ~spl4_13),
% 1.54/0.58    inference(avatar_split_clause,[],[f428,f144,f436,f432])).
% 1.54/0.58  fof(f144,plain,(
% 1.54/0.58    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.54/0.58  fof(f428,plain,(
% 1.54/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 1.54/0.58    inference(resolution,[],[f181,f146])).
% 1.54/0.58  fof(f146,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 1.54/0.58    inference(avatar_component_clause,[],[f144])).
% 1.54/0.58  fof(f415,plain,(
% 1.54/0.58    spl4_40 | ~spl4_37),
% 1.54/0.58    inference(avatar_split_clause,[],[f414,f380,f410])).
% 1.54/0.58  fof(f380,plain,(
% 1.54/0.58    spl4_37 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.54/0.58  fof(f414,plain,(
% 1.54/0.58    sK1 = k2_relat_1(sK2) | ~spl4_37),
% 1.54/0.58    inference(forward_demodulation,[],[f397,f74])).
% 1.54/0.58  fof(f74,plain,(
% 1.54/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f1])).
% 1.54/0.58  fof(f397,plain,(
% 1.54/0.58    k2_relat_1(sK2) = k1_relat_1(k6_relat_1(sK1)) | ~spl4_37),
% 1.54/0.58    inference(superposition,[],[f74,f382])).
% 1.54/0.58  fof(f382,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~spl4_37),
% 1.54/0.58    inference(avatar_component_clause,[],[f380])).
% 1.54/0.58  fof(f387,plain,(
% 1.54/0.58    spl4_37 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27),
% 1.54/0.58    inference(avatar_split_clause,[],[f386,f274,f157,f138,f98,f380])).
% 1.54/0.58  fof(f274,plain,(
% 1.54/0.58    spl4_27 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.54/0.58  fof(f386,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_27)),
% 1.54/0.58    inference(subsumption_resolution,[],[f385,f159])).
% 1.54/0.58  fof(f385,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_27)),
% 1.54/0.58    inference(subsumption_resolution,[],[f384,f140])).
% 1.54/0.58  fof(f384,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_27)),
% 1.54/0.58    inference(subsumption_resolution,[],[f374,f100])).
% 1.54/0.58  fof(f374,plain,(
% 1.54/0.58    k6_relat_1(sK1) = k6_relat_1(k2_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_27),
% 1.54/0.58    inference(superposition,[],[f59,f276])).
% 1.54/0.58  fof(f276,plain,(
% 1.54/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_27),
% 1.54/0.58    inference(avatar_component_clause,[],[f274])).
% 1.54/0.58  fof(f362,plain,(
% 1.54/0.58    spl4_36 | ~spl4_33 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_32),
% 1.54/0.58    inference(avatar_split_clause,[],[f357,f322,f123,f118,f113,f93,f338,f359])).
% 1.54/0.58  fof(f322,plain,(
% 1.54/0.58    spl4_32 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.54/0.58  fof(f357,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f356,f125])).
% 1.54/0.58  fof(f356,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f355,f120])).
% 1.54/0.58  fof(f355,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f354,f115])).
% 1.54/0.58  fof(f354,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f331,f95])).
% 1.54/0.58  fof(f331,plain,(
% 1.54/0.58    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_32),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f330])).
% 1.54/0.58  fof(f330,plain,(
% 1.54/0.58    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_32),
% 1.54/0.58    inference(superposition,[],[f210,f324])).
% 1.54/0.58  fof(f324,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_32),
% 1.54/0.58    inference(avatar_component_clause,[],[f322])).
% 1.54/0.58  fof(f210,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f55,f69])).
% 1.54/0.58  fof(f69,plain,(
% 1.54/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f11])).
% 1.54/0.58  fof(f11,axiom,(
% 1.54/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.54/0.58  fof(f55,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f20])).
% 1.54/0.58  fof(f20,plain,(
% 1.54/0.58    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.58    inference(flattening,[],[f19])).
% 1.54/0.58  fof(f19,plain,(
% 1.54/0.58    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.58    inference(ennf_transformation,[],[f14])).
% 1.54/0.58  fof(f14,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.54/0.58  fof(f353,plain,(
% 1.54/0.58    spl4_35 | ~spl4_33 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_32),
% 1.54/0.58    inference(avatar_split_clause,[],[f348,f322,f123,f118,f113,f93,f338,f350])).
% 1.54/0.58  fof(f348,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f347,f125])).
% 1.54/0.58  fof(f347,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f346,f120])).
% 1.54/0.58  fof(f346,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f345,f115])).
% 1.54/0.58  fof(f345,plain,(
% 1.54/0.58    ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_32)),
% 1.54/0.58    inference(subsumption_resolution,[],[f332,f95])).
% 1.54/0.58  fof(f332,plain,(
% 1.54/0.58    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_32),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f329])).
% 1.54/0.58  fof(f329,plain,(
% 1.54/0.58    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_32),
% 1.54/0.58    inference(superposition,[],[f211,f324])).
% 1.54/0.58  fof(f211,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f56,f69])).
% 1.54/0.58  fof(f56,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f20])).
% 1.54/0.58  fof(f325,plain,(
% 1.54/0.58    spl4_32 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 1.54/0.58    inference(avatar_split_clause,[],[f320,f144,f138,f133,f128,f123,f118,f113,f322])).
% 1.54/0.58  fof(f320,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f319,f125])).
% 1.54/0.58  fof(f319,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f318,f120])).
% 1.54/0.58  fof(f318,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f317,f115])).
% 1.54/0.58  fof(f317,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f316,f140])).
% 1.54/0.58  fof(f316,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f315,f135])).
% 1.54/0.58  fof(f315,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f312,f130])).
% 1.54/0.58  fof(f312,plain,(
% 1.54/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 1.54/0.58    inference(resolution,[],[f308,f146])).
% 1.54/0.58  fof(f308,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.58    inference(forward_demodulation,[],[f68,f69])).
% 1.54/0.58  fof(f68,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f32])).
% 1.54/0.58  fof(f32,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.58    inference(flattening,[],[f31])).
% 1.54/0.58  fof(f31,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.58    inference(ennf_transformation,[],[f12])).
% 1.54/0.58  fof(f12,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.54/0.58  fof(f307,plain,(
% 1.54/0.58    spl4_31 | ~spl4_20),
% 1.54/0.58    inference(avatar_split_clause,[],[f306,f231,f302])).
% 1.54/0.58  fof(f231,plain,(
% 1.54/0.58    spl4_20 <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.54/0.58  fof(f306,plain,(
% 1.54/0.58    sK0 = k1_relat_1(sK2) | ~spl4_20),
% 1.54/0.58    inference(forward_demodulation,[],[f283,f74])).
% 1.54/0.58  fof(f283,plain,(
% 1.54/0.58    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~spl4_20),
% 1.54/0.58    inference(superposition,[],[f74,f233])).
% 1.54/0.58  fof(f233,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~spl4_20),
% 1.54/0.58    inference(avatar_component_clause,[],[f231])).
% 1.54/0.58  fof(f289,plain,(
% 1.54/0.58    spl4_28 | ~spl4_15 | ~spl4_20),
% 1.54/0.58    inference(avatar_split_clause,[],[f284,f231,f157,f286])).
% 1.54/0.58  fof(f284,plain,(
% 1.54/0.58    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | (~spl4_15 | ~spl4_20)),
% 1.54/0.58    inference(subsumption_resolution,[],[f278,f159])).
% 1.54/0.58  fof(f278,plain,(
% 1.54/0.58    sK2 = k5_relat_1(k6_relat_1(sK0),sK2) | ~v1_relat_1(sK2) | ~spl4_20),
% 1.54/0.58    inference(superposition,[],[f73,f233])).
% 1.54/0.58  fof(f73,plain,(
% 1.54/0.58    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f37])).
% 1.54/0.58  fof(f37,plain,(
% 1.54/0.58    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.54/0.58    inference(ennf_transformation,[],[f2])).
% 1.54/0.58  fof(f2,axiom,(
% 1.54/0.58    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.54/0.58  fof(f277,plain,(
% 1.54/0.58    spl4_27 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.54/0.58    inference(avatar_split_clause,[],[f272,f138,f133,f128,f108,f98,f88,f274])).
% 1.54/0.58  fof(f88,plain,(
% 1.54/0.58    spl4_2 <=> k1_xboole_0 = sK1),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.54/0.58  fof(f272,plain,(
% 1.54/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.54/0.58    inference(subsumption_resolution,[],[f271,f140])).
% 1.54/0.58  fof(f271,plain,(
% 1.54/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.54/0.58    inference(subsumption_resolution,[],[f270,f135])).
% 1.54/0.58  fof(f270,plain,(
% 1.54/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.54/0.58    inference(subsumption_resolution,[],[f269,f130])).
% 1.54/0.58  fof(f269,plain,(
% 1.54/0.58    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.54/0.58    inference(subsumption_resolution,[],[f268,f100])).
% 1.54/0.58  fof(f268,plain,(
% 1.54/0.58    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.54/0.58    inference(subsumption_resolution,[],[f267,f90])).
% 1.54/0.58  fof(f90,plain,(
% 1.54/0.58    k1_xboole_0 != sK1 | spl4_2),
% 1.54/0.58    inference(avatar_component_clause,[],[f88])).
% 1.54/0.58  fof(f267,plain,(
% 1.54/0.58    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f266])).
% 1.54/0.58  fof(f266,plain,(
% 1.54/0.58    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.54/0.58    inference(superposition,[],[f211,f110])).
% 1.54/0.58  fof(f238,plain,(
% 1.54/0.58    spl4_20 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19),
% 1.54/0.58    inference(avatar_split_clause,[],[f237,f220,f157,f138,f98,f231])).
% 1.54/0.58  fof(f220,plain,(
% 1.54/0.58    spl4_19 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.54/0.58  fof(f237,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19)),
% 1.54/0.58    inference(subsumption_resolution,[],[f236,f159])).
% 1.54/0.58  fof(f236,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_19)),
% 1.54/0.58    inference(subsumption_resolution,[],[f235,f140])).
% 1.54/0.58  fof(f235,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_19)),
% 1.54/0.58    inference(subsumption_resolution,[],[f225,f100])).
% 1.54/0.58  fof(f225,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_19),
% 1.54/0.58    inference(superposition,[],[f58,f222])).
% 1.54/0.58  fof(f222,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_19),
% 1.54/0.58    inference(avatar_component_clause,[],[f220])).
% 1.54/0.58  fof(f223,plain,(
% 1.54/0.58    spl4_19 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.54/0.58    inference(avatar_split_clause,[],[f218,f138,f133,f128,f108,f98,f88,f220])).
% 1.54/0.58  fof(f218,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.54/0.58    inference(subsumption_resolution,[],[f217,f140])).
% 1.54/0.58  fof(f217,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.54/0.58    inference(subsumption_resolution,[],[f216,f135])).
% 1.54/0.58  fof(f216,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.54/0.58    inference(subsumption_resolution,[],[f215,f130])).
% 1.54/0.58  fof(f215,plain,(
% 1.54/0.58    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.54/0.58    inference(subsumption_resolution,[],[f214,f100])).
% 1.54/0.58  fof(f214,plain,(
% 1.54/0.58    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.54/0.58    inference(subsumption_resolution,[],[f213,f90])).
% 1.54/0.58  fof(f213,plain,(
% 1.54/0.58    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.54/0.58    inference(trivial_inequality_removal,[],[f212])).
% 1.54/0.58  fof(f212,plain,(
% 1.54/0.58    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.54/0.58    inference(superposition,[],[f210,f110])).
% 1.54/0.58  fof(f202,plain,(
% 1.54/0.58    spl4_18 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.54/0.58    inference(avatar_split_clause,[],[f197,f144,f138,f128,f123,f113,f199])).
% 1.54/0.58  fof(f197,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f196,f140])).
% 1.54/0.58  fof(f196,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f195,f130])).
% 1.54/0.58  fof(f195,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f194,f125])).
% 1.54/0.58  fof(f194,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.54/0.58    inference(subsumption_resolution,[],[f191,f115])).
% 1.54/0.58  fof(f191,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.54/0.58    inference(superposition,[],[f146,f72])).
% 1.54/0.58  fof(f160,plain,(
% 1.54/0.58    spl4_15 | ~spl4_10),
% 1.54/0.58    inference(avatar_split_clause,[],[f149,f128,f157])).
% 1.54/0.58  fof(f149,plain,(
% 1.54/0.58    v1_relat_1(sK2) | ~spl4_10),
% 1.54/0.58    inference(resolution,[],[f76,f130])).
% 1.54/0.58  fof(f155,plain,(
% 1.54/0.58    spl4_14 | ~spl4_7),
% 1.54/0.58    inference(avatar_split_clause,[],[f148,f113,f152])).
% 1.54/0.58  fof(f148,plain,(
% 1.54/0.58    v1_relat_1(sK3) | ~spl4_7),
% 1.54/0.58    inference(resolution,[],[f76,f115])).
% 1.54/0.58  fof(f147,plain,(
% 1.54/0.58    spl4_13 | ~spl4_5),
% 1.54/0.58    inference(avatar_split_clause,[],[f142,f103,f144])).
% 1.54/0.58  fof(f103,plain,(
% 1.54/0.58    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.54/0.58  fof(f142,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.54/0.58    inference(backward_demodulation,[],[f105,f69])).
% 1.54/0.58  fof(f105,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.54/0.58    inference(avatar_component_clause,[],[f103])).
% 1.54/0.58  fof(f141,plain,(
% 1.54/0.58    spl4_12),
% 1.54/0.58    inference(avatar_split_clause,[],[f43,f138])).
% 1.54/0.58  fof(f43,plain,(
% 1.54/0.58    v1_funct_1(sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f41,plain,(
% 1.54/0.58    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f40,f39])).
% 1.54/0.58  fof(f39,plain,(
% 1.54/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f40,plain,(
% 1.54/0.58    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f18,plain,(
% 1.54/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.54/0.58    inference(flattening,[],[f17])).
% 1.54/0.58  fof(f17,plain,(
% 1.54/0.58    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.54/0.58    inference(ennf_transformation,[],[f16])).
% 1.54/0.58  fof(f16,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.54/0.58    inference(negated_conjecture,[],[f15])).
% 1.54/0.58  fof(f15,conjecture,(
% 1.54/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.54/0.58  fof(f136,plain,(
% 1.54/0.58    spl4_11),
% 1.54/0.58    inference(avatar_split_clause,[],[f44,f133])).
% 1.54/0.58  fof(f44,plain,(
% 1.54/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f131,plain,(
% 1.54/0.58    spl4_10),
% 1.54/0.58    inference(avatar_split_clause,[],[f45,f128])).
% 1.54/0.58  fof(f45,plain,(
% 1.54/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f126,plain,(
% 1.54/0.58    spl4_9),
% 1.54/0.58    inference(avatar_split_clause,[],[f46,f123])).
% 1.54/0.58  fof(f46,plain,(
% 1.54/0.58    v1_funct_1(sK3)),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f121,plain,(
% 1.54/0.58    spl4_8),
% 1.54/0.58    inference(avatar_split_clause,[],[f47,f118])).
% 1.54/0.58  fof(f47,plain,(
% 1.54/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f116,plain,(
% 1.54/0.58    spl4_7),
% 1.54/0.58    inference(avatar_split_clause,[],[f48,f113])).
% 1.54/0.58  fof(f48,plain,(
% 1.54/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f111,plain,(
% 1.54/0.58    spl4_6),
% 1.54/0.58    inference(avatar_split_clause,[],[f49,f108])).
% 1.54/0.58  fof(f49,plain,(
% 1.54/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f106,plain,(
% 1.54/0.58    spl4_5),
% 1.54/0.58    inference(avatar_split_clause,[],[f50,f103])).
% 1.54/0.58  fof(f50,plain,(
% 1.54/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f101,plain,(
% 1.54/0.58    spl4_4),
% 1.54/0.58    inference(avatar_split_clause,[],[f51,f98])).
% 1.54/0.58  fof(f51,plain,(
% 1.54/0.58    v2_funct_1(sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f96,plain,(
% 1.54/0.58    ~spl4_3),
% 1.54/0.58    inference(avatar_split_clause,[],[f52,f93])).
% 1.54/0.58  fof(f52,plain,(
% 1.54/0.58    k1_xboole_0 != sK0),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f91,plain,(
% 1.54/0.58    ~spl4_2),
% 1.54/0.58    inference(avatar_split_clause,[],[f53,f88])).
% 1.54/0.58  fof(f53,plain,(
% 1.54/0.58    k1_xboole_0 != sK1),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  fof(f86,plain,(
% 1.54/0.58    ~spl4_1),
% 1.54/0.58    inference(avatar_split_clause,[],[f54,f83])).
% 1.54/0.58  fof(f83,plain,(
% 1.54/0.58    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 1.54/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.54/0.58  fof(f54,plain,(
% 1.54/0.58    k2_funct_1(sK2) != sK3),
% 1.54/0.58    inference(cnf_transformation,[],[f41])).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (16405)------------------------------
% 1.54/0.58  % (16405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (16405)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (16405)Memory used [KB]: 7291
% 1.54/0.58  % (16405)Time elapsed: 0.168 s
% 1.54/0.58  % (16405)------------------------------
% 1.54/0.58  % (16405)------------------------------
% 1.54/0.59  % (16379)Success in time 0.238 s
%------------------------------------------------------------------------------
