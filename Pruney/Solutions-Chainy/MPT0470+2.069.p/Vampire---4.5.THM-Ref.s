%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 357 expanded)
%              Number of leaves         :   58 ( 166 expanded)
%              Depth                    :    7
%              Number of atoms          :  586 ( 922 expanded)
%              Number of equality atoms :  121 ( 201 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1080,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f77,f82,f87,f91,f95,f99,f103,f108,f112,f148,f154,f158,f168,f187,f215,f219,f229,f246,f273,f293,f298,f376,f406,f508,f559,f739,f749,f797,f883,f903,f911,f921,f1025,f1049,f1054,f1067])).

fof(f1067,plain,
    ( ~ spl1_7
    | spl1_19
    | ~ spl1_89 ),
    inference(avatar_contradiction_clause,[],[f1066])).

fof(f1066,plain,
    ( $false
    | ~ spl1_7
    | spl1_19
    | ~ spl1_89 ),
    inference(subsumption_resolution,[],[f1056,f163])).

fof(f163,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl1_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl1_19
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f1056,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl1_7
    | ~ spl1_89 ),
    inference(resolution,[],[f1044,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl1_7
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f1044,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_89 ),
    inference(avatar_component_clause,[],[f1042])).

fof(f1042,plain,
    ( spl1_89
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_89])])).

fof(f1054,plain,
    ( ~ spl1_1
    | ~ spl1_16
    | ~ spl1_17
    | spl1_90 ),
    inference(avatar_contradiction_clause,[],[f1053])).

fof(f1053,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_16
    | ~ spl1_17
    | spl1_90 ),
    inference(subsumption_resolution,[],[f1052,f141])).

fof(f141,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl1_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f1052,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_17
    | spl1_90 ),
    inference(subsumption_resolution,[],[f1050,f67])).

fof(f67,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f1050,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl1_17
    | spl1_90 ),
    inference(resolution,[],[f1048,f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl1_17
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f1048,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | spl1_90 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f1046,plain,
    ( spl1_90
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_90])])).

fof(f1049,plain,
    ( spl1_89
    | ~ spl1_90
    | ~ spl1_2
    | ~ spl1_11
    | ~ spl1_84 ),
    inference(avatar_split_clause,[],[f906,f900,f110,f70,f1046,f1042])).

fof(f70,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f110,plain,
    ( spl1_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f900,plain,
    ( spl1_84
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_84])])).

fof(f906,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_2
    | ~ spl1_11
    | ~ spl1_84 ),
    inference(subsumption_resolution,[],[f905,f72])).

fof(f72,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f905,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_11
    | ~ spl1_84 ),
    inference(superposition,[],[f111,f902])).

fof(f902,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_84 ),
    inference(avatar_component_clause,[],[f900])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1025,plain,
    ( spl1_20
    | ~ spl1_7
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_86 ),
    inference(avatar_split_clause,[],[f954,f918,f556,f243,f93,f165])).

fof(f165,plain,
    ( spl1_20
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f243,plain,
    ( spl1_30
  <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).

fof(f556,plain,
    ( spl1_52
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).

fof(f918,plain,
    ( spl1_86
  <=> v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_86])])).

fof(f954,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_30
    | ~ spl1_52
    | ~ spl1_86 ),
    inference(forward_demodulation,[],[f932,f558])).

fof(f558,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_52 ),
    inference(avatar_component_clause,[],[f556])).

fof(f932,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_30
    | ~ spl1_86 ),
    inference(backward_demodulation,[],[f245,f922])).

fof(f922,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_7
    | ~ spl1_86 ),
    inference(resolution,[],[f920,f94])).

fof(f920,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_86 ),
    inference(avatar_component_clause,[],[f918])).

fof(f245,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_30 ),
    inference(avatar_component_clause,[],[f243])).

fof(f921,plain,
    ( spl1_86
    | ~ spl1_2
    | ~ spl1_11
    | ~ spl1_34
    | ~ spl1_85 ),
    inference(avatar_split_clause,[],[f916,f908,f283,f110,f70,f918])).

fof(f283,plain,
    ( spl1_34
  <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).

fof(f908,plain,
    ( spl1_85
  <=> k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_85])])).

fof(f916,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_2
    | ~ spl1_11
    | ~ spl1_34
    | ~ spl1_85 ),
    inference(subsumption_resolution,[],[f915,f284])).

fof(f284,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_34 ),
    inference(avatar_component_clause,[],[f283])).

fof(f915,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_2
    | ~ spl1_11
    | ~ spl1_85 ),
    inference(subsumption_resolution,[],[f913,f72])).

fof(f913,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_11
    | ~ spl1_85 ),
    inference(superposition,[],[f111,f910])).

fof(f910,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_85 ),
    inference(avatar_component_clause,[],[f908])).

fof(f911,plain,
    ( spl1_85
    | ~ spl1_45
    | ~ spl1_74
    | ~ spl1_83 ),
    inference(avatar_split_clause,[],[f898,f881,f794,f399,f908])).

fof(f399,plain,
    ( spl1_45
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_45])])).

fof(f794,plain,
    ( spl1_74
  <=> k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_74])])).

fof(f881,plain,
    ( spl1_83
  <=> ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_83])])).

fof(f898,plain,
    ( k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_45
    | ~ spl1_74
    | ~ spl1_83 ),
    inference(forward_demodulation,[],[f891,f796])).

fof(f796,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_74 ),
    inference(avatar_component_clause,[],[f794])).

fof(f891,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ spl1_45
    | ~ spl1_83 ),
    inference(resolution,[],[f882,f400])).

fof(f400,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl1_45 ),
    inference(avatar_component_clause,[],[f399])).

fof(f882,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) )
    | ~ spl1_83 ),
    inference(avatar_component_clause,[],[f881])).

fof(f903,plain,
    ( spl1_84
    | ~ spl1_1
    | ~ spl1_83 ),
    inference(avatar_split_clause,[],[f897,f881,f65,f900])).

fof(f897,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ spl1_1
    | ~ spl1_83 ),
    inference(resolution,[],[f882,f67])).

fof(f883,plain,
    ( spl1_83
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_16
    | ~ spl1_71 ),
    inference(avatar_split_clause,[],[f872,f737,f139,f84,f79,f75,f881])).

fof(f75,plain,
    ( spl1_3
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f79,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f84,plain,
    ( spl1_5
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f737,plain,
    ( spl1_71
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_71])])).

fof(f872,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_16
    | ~ spl1_71 ),
    inference(forward_demodulation,[],[f871,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f871,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_16
    | ~ spl1_71 ),
    inference(subsumption_resolution,[],[f870,f141])).

fof(f870,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_71 ),
    inference(subsumption_resolution,[],[f868,f76])).

fof(f76,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f868,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
        | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_5
    | ~ spl1_71 ),
    inference(superposition,[],[f738,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f738,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
        | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_71 ),
    inference(avatar_component_clause,[],[f737])).

fof(f797,plain,
    ( spl1_74
    | ~ spl1_16
    | ~ spl1_52
    | ~ spl1_73 ),
    inference(avatar_split_clause,[],[f765,f747,f556,f139,f794])).

fof(f747,plain,
    ( spl1_73
  <=> ! [X17] :
        ( ~ v1_relat_1(X17)
        | k4_relat_1(k5_relat_1(sK0,X17)) = k5_relat_1(k4_relat_1(X17),k4_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_73])])).

fof(f765,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ spl1_16
    | ~ spl1_52
    | ~ spl1_73 ),
    inference(forward_demodulation,[],[f751,f558])).

fof(f751,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))
    | ~ spl1_16
    | ~ spl1_73 ),
    inference(resolution,[],[f748,f141])).

fof(f748,plain,
    ( ! [X17] :
        ( ~ v1_relat_1(X17)
        | k4_relat_1(k5_relat_1(sK0,X17)) = k5_relat_1(k4_relat_1(X17),k4_relat_1(sK0)) )
    | ~ spl1_73 ),
    inference(avatar_component_clause,[],[f747])).

fof(f749,plain,
    ( spl1_73
    | ~ spl1_1
    | ~ spl1_41 ),
    inference(avatar_split_clause,[],[f641,f374,f65,f747])).

fof(f374,plain,
    ( spl1_41
  <=> ! [X1,X0] :
        ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).

fof(f641,plain,
    ( ! [X17] :
        ( ~ v1_relat_1(X17)
        | k4_relat_1(k5_relat_1(sK0,X17)) = k5_relat_1(k4_relat_1(X17),k4_relat_1(sK0)) )
    | ~ spl1_1
    | ~ spl1_41 ),
    inference(resolution,[],[f375,f67])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) )
    | ~ spl1_41 ),
    inference(avatar_component_clause,[],[f374])).

fof(f739,plain,(
    spl1_71 ),
    inference(avatar_split_clause,[],[f51,f737])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f559,plain,
    ( spl1_52
    | ~ spl1_1
    | ~ spl1_26
    | ~ spl1_51 ),
    inference(avatar_split_clause,[],[f536,f506,f213,f65,f556])).

fof(f213,plain,
    ( spl1_26
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).

fof(f506,plain,
    ( spl1_51
  <=> ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).

fof(f536,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_26
    | ~ spl1_51 ),
    inference(forward_demodulation,[],[f535,f214])).

fof(f214,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)
    | ~ spl1_26 ),
    inference(avatar_component_clause,[],[f213])).

fof(f535,plain,
    ( k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0))
    | ~ spl1_1
    | ~ spl1_26
    | ~ spl1_51 ),
    inference(forward_demodulation,[],[f525,f214])).

fof(f525,plain,
    ( k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_51 ),
    inference(resolution,[],[f507,f67])).

fof(f507,plain,
    ( ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) )
    | ~ spl1_51 ),
    inference(avatar_component_clause,[],[f506])).

fof(f508,plain,
    ( spl1_51
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(avatar_split_clause,[],[f479,f271,f65,f506])).

fof(f271,plain,
    ( spl1_33
  <=> ! [X1,X0] :
        ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).

fof(f479,plain,
    ( ! [X18] :
        ( ~ v1_relat_1(X18)
        | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)) )
    | ~ spl1_1
    | ~ spl1_33 ),
    inference(resolution,[],[f272,f67])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) )
    | ~ spl1_33 ),
    inference(avatar_component_clause,[],[f271])).

fof(f406,plain,
    ( ~ spl1_1
    | ~ spl1_8
    | spl1_45 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_8
    | spl1_45 ),
    inference(subsumption_resolution,[],[f403,f67])).

fof(f403,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_8
    | spl1_45 ),
    inference(resolution,[],[f401,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl1_8
  <=> ! [X0] :
        ( v1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f401,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl1_45 ),
    inference(avatar_component_clause,[],[f399])).

fof(f376,plain,(
    spl1_41 ),
    inference(avatar_split_clause,[],[f50,f374])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f298,plain,
    ( ~ spl1_1
    | ~ spl1_16
    | ~ spl1_17
    | spl1_35 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl1_1
    | ~ spl1_16
    | ~ spl1_17
    | spl1_35 ),
    inference(subsumption_resolution,[],[f296,f67])).

fof(f296,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl1_16
    | ~ spl1_17
    | spl1_35 ),
    inference(subsumption_resolution,[],[f294,f141])).

fof(f294,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_17
    | spl1_35 ),
    inference(resolution,[],[f288,f153])).

fof(f288,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl1_35 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl1_35
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).

fof(f293,plain,
    ( ~ spl1_35
    | ~ spl1_8
    | spl1_34 ),
    inference(avatar_split_clause,[],[f291,f283,f97,f287])).

fof(f291,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl1_8
    | spl1_34 ),
    inference(resolution,[],[f285,f98])).

fof(f285,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | spl1_34 ),
    inference(avatar_component_clause,[],[f283])).

fof(f273,plain,(
    spl1_33 ),
    inference(avatar_split_clause,[],[f49,f271])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f246,plain,
    ( spl1_30
    | ~ spl1_16
    | ~ spl1_28 ),
    inference(avatar_split_clause,[],[f231,f227,f139,f243])).

fof(f227,plain,
    ( spl1_28
  <=> ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f231,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | ~ spl1_16
    | ~ spl1_28 ),
    inference(resolution,[],[f228,f141])).

fof(f228,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_28 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl1_28
    | ~ spl1_1
    | ~ spl1_27 ),
    inference(avatar_split_clause,[],[f225,f217,f65,f227])).

fof(f217,plain,
    ( spl1_27
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f225,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(X9)
        | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))) )
    | ~ spl1_1
    | ~ spl1_27 ),
    inference(resolution,[],[f218,f67])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_27 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl1_27
    | ~ spl1_10
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f159,f152,f106,f217])).

fof(f106,plain,
    ( spl1_10
  <=> ! [X0] :
        ( k4_relat_1(k4_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) )
    | ~ spl1_10
    | ~ spl1_17 ),
    inference(resolution,[],[f153,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k4_relat_1(X0)) = X0 )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f215,plain,
    ( spl1_26
    | ~ spl1_9
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(avatar_split_clause,[],[f210,f185,f156,f101,f213])).

fof(f101,plain,
    ( spl1_9
  <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f156,plain,
    ( spl1_18
  <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f185,plain,
    ( spl1_23
  <=> ! [X1,X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).

fof(f210,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)
    | ~ spl1_9
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(forward_demodulation,[],[f208,f102])).

fof(f102,plain,
    ( ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f208,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))
    | ~ spl1_18
    | ~ spl1_23 ),
    inference(superposition,[],[f186,f157])).

fof(f157,plain,
    ( ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f186,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))
    | ~ spl1_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,(
    spl1_23 ),
    inference(avatar_split_clause,[],[f63,f185])).

fof(f63,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f56,f53,f53,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f168,plain,
    ( ~ spl1_19
    | ~ spl1_20 ),
    inference(avatar_split_clause,[],[f38,f165,f161])).

fof(f38,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f158,plain,(
    spl1_18 ),
    inference(avatar_split_clause,[],[f61,f156])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f154,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f57,f152])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f148,plain,
    ( ~ spl1_2
    | ~ spl1_6
    | spl1_16 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_6
    | spl1_16 ),
    inference(subsumption_resolution,[],[f146,f72])).

fof(f146,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl1_6
    | spl1_16 ),
    inference(resolution,[],[f140,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl1_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f140,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f112,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f52,f110])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f108,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f48,f106])).

fof(f48,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f103,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f62,f101])).

fof(f62,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f99,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f95,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f46,f93])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f91,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f87,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f82,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f73,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f68,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (20755)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (20753)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (20744)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (20754)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (20756)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (20742)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (20747)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (20748)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (20743)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (20752)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (20749)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (20745)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.53  % (20758)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (20757)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (20746)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (20751)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (20750)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.55  % (20759)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.56  % (20749)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f1080,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f68,f73,f77,f82,f87,f91,f95,f99,f103,f108,f112,f148,f154,f158,f168,f187,f215,f219,f229,f246,f273,f293,f298,f376,f406,f508,f559,f739,f749,f797,f883,f903,f911,f921,f1025,f1049,f1054,f1067])).
% 0.21/0.57  fof(f1067,plain,(
% 0.21/0.57    ~spl1_7 | spl1_19 | ~spl1_89),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1066])).
% 0.21/0.57  fof(f1066,plain,(
% 0.21/0.57    $false | (~spl1_7 | spl1_19 | ~spl1_89)),
% 0.21/0.57    inference(subsumption_resolution,[],[f1056,f163])).
% 0.21/0.57  fof(f163,plain,(
% 0.21/0.57    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl1_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f161])).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    spl1_19 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.21/0.57  fof(f1056,plain,(
% 0.21/0.57    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl1_7 | ~spl1_89)),
% 0.21/0.57    inference(resolution,[],[f1044,f94])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl1_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f93])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    spl1_7 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.57  fof(f1044,plain,(
% 0.21/0.57    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_89),
% 0.21/0.57    inference(avatar_component_clause,[],[f1042])).
% 0.21/0.57  fof(f1042,plain,(
% 0.21/0.57    spl1_89 <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_89])])).
% 0.21/0.57  fof(f1054,plain,(
% 0.21/0.57    ~spl1_1 | ~spl1_16 | ~spl1_17 | spl1_90),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f1053])).
% 0.21/0.57  fof(f1053,plain,(
% 0.21/0.57    $false | (~spl1_1 | ~spl1_16 | ~spl1_17 | spl1_90)),
% 0.21/0.57    inference(subsumption_resolution,[],[f1052,f141])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    v1_relat_1(k1_xboole_0) | ~spl1_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f139])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    spl1_16 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.57  fof(f1052,plain,(
% 0.21/0.57    ~v1_relat_1(k1_xboole_0) | (~spl1_1 | ~spl1_17 | spl1_90)),
% 0.21/0.57    inference(subsumption_resolution,[],[f1050,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.57  fof(f1050,plain,(
% 0.21/0.57    ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0) | (~spl1_17 | spl1_90)),
% 0.21/0.57    inference(resolution,[],[f1048,f153])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f152])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    spl1_17 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.57  fof(f1048,plain,(
% 0.21/0.57    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | spl1_90),
% 0.21/0.57    inference(avatar_component_clause,[],[f1046])).
% 0.21/0.57  fof(f1046,plain,(
% 0.21/0.57    spl1_90 <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_90])])).
% 0.21/0.57  fof(f1049,plain,(
% 0.21/0.57    spl1_89 | ~spl1_90 | ~spl1_2 | ~spl1_11 | ~spl1_84),
% 0.21/0.57    inference(avatar_split_clause,[],[f906,f900,f110,f70,f1046,f1042])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    spl1_11 <=> ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.57  fof(f900,plain,(
% 0.21/0.57    spl1_84 <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_84])])).
% 0.21/0.57  fof(f906,plain,(
% 0.21/0.57    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_2 | ~spl1_11 | ~spl1_84)),
% 0.21/0.57    inference(subsumption_resolution,[],[f905,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f70])).
% 0.21/0.57  fof(f905,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_11 | ~spl1_84)),
% 0.21/0.57    inference(superposition,[],[f111,f902])).
% 0.21/0.57  fof(f902,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | ~spl1_84),
% 0.21/0.57    inference(avatar_component_clause,[],[f900])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) ) | ~spl1_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f110])).
% 0.21/0.57  fof(f1025,plain,(
% 0.21/0.57    spl1_20 | ~spl1_7 | ~spl1_30 | ~spl1_52 | ~spl1_86),
% 0.21/0.57    inference(avatar_split_clause,[],[f954,f918,f556,f243,f93,f165])).
% 0.21/0.57  fof(f165,plain,(
% 0.21/0.57    spl1_20 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.21/0.57  fof(f243,plain,(
% 0.21/0.57    spl1_30 <=> k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_30])])).
% 0.21/0.57  fof(f556,plain,(
% 0.21/0.57    spl1_52 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_52])])).
% 0.21/0.57  fof(f918,plain,(
% 0.21/0.57    spl1_86 <=> v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_86])])).
% 0.21/0.57  fof(f954,plain,(
% 0.21/0.57    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl1_7 | ~spl1_30 | ~spl1_52 | ~spl1_86)),
% 0.21/0.57    inference(forward_demodulation,[],[f932,f558])).
% 0.21/0.57  fof(f558,plain,(
% 0.21/0.57    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl1_52),
% 0.21/0.57    inference(avatar_component_clause,[],[f556])).
% 0.21/0.57  fof(f932,plain,(
% 0.21/0.57    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) | (~spl1_7 | ~spl1_30 | ~spl1_86)),
% 0.21/0.57    inference(backward_demodulation,[],[f245,f922])).
% 0.21/0.57  fof(f922,plain,(
% 0.21/0.57    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_7 | ~spl1_86)),
% 0.21/0.57    inference(resolution,[],[f920,f94])).
% 0.21/0.57  fof(f920,plain,(
% 0.21/0.57    v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_86),
% 0.21/0.57    inference(avatar_component_clause,[],[f918])).
% 0.21/0.57  fof(f245,plain,(
% 0.21/0.57    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_30),
% 0.21/0.57    inference(avatar_component_clause,[],[f243])).
% 0.21/0.57  fof(f921,plain,(
% 0.21/0.57    spl1_86 | ~spl1_2 | ~spl1_11 | ~spl1_34 | ~spl1_85),
% 0.21/0.57    inference(avatar_split_clause,[],[f916,f908,f283,f110,f70,f918])).
% 0.21/0.57  fof(f283,plain,(
% 0.21/0.57    spl1_34 <=> v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_34])])).
% 0.21/0.57  fof(f908,plain,(
% 0.21/0.57    spl1_85 <=> k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_85])])).
% 0.21/0.57  fof(f916,plain,(
% 0.21/0.57    v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_2 | ~spl1_11 | ~spl1_34 | ~spl1_85)),
% 0.21/0.57    inference(subsumption_resolution,[],[f915,f284])).
% 0.21/0.57  fof(f284,plain,(
% 0.21/0.57    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_34),
% 0.21/0.57    inference(avatar_component_clause,[],[f283])).
% 0.21/0.57  fof(f915,plain,(
% 0.21/0.57    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_2 | ~spl1_11 | ~spl1_85)),
% 0.21/0.57    inference(subsumption_resolution,[],[f913,f72])).
% 0.21/0.57  fof(f913,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_11 | ~spl1_85)),
% 0.21/0.57    inference(superposition,[],[f111,f910])).
% 0.21/0.57  fof(f910,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | ~spl1_85),
% 0.21/0.57    inference(avatar_component_clause,[],[f908])).
% 0.21/0.57  fof(f911,plain,(
% 0.21/0.57    spl1_85 | ~spl1_45 | ~spl1_74 | ~spl1_83),
% 0.21/0.57    inference(avatar_split_clause,[],[f898,f881,f794,f399,f908])).
% 0.21/0.57  fof(f399,plain,(
% 0.21/0.57    spl1_45 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_45])])).
% 0.21/0.57  fof(f794,plain,(
% 0.21/0.57    spl1_74 <=> k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_74])])).
% 0.21/0.57  fof(f881,plain,(
% 0.21/0.57    spl1_83 <=> ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_83])])).
% 0.21/0.57  fof(f898,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_45 | ~spl1_74 | ~spl1_83)),
% 0.21/0.57    inference(forward_demodulation,[],[f891,f796])).
% 0.21/0.57  fof(f796,plain,(
% 0.21/0.57    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~spl1_74),
% 0.21/0.57    inference(avatar_component_clause,[],[f794])).
% 0.21/0.57  fof(f891,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | (~spl1_45 | ~spl1_83)),
% 0.21/0.57    inference(resolution,[],[f882,f400])).
% 0.21/0.57  fof(f400,plain,(
% 0.21/0.57    v1_relat_1(k4_relat_1(sK0)) | ~spl1_45),
% 0.21/0.57    inference(avatar_component_clause,[],[f399])).
% 0.21/0.57  fof(f882,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) ) | ~spl1_83),
% 0.21/0.57    inference(avatar_component_clause,[],[f881])).
% 0.21/0.57  fof(f903,plain,(
% 0.21/0.57    spl1_84 | ~spl1_1 | ~spl1_83),
% 0.21/0.57    inference(avatar_split_clause,[],[f897,f881,f65,f900])).
% 0.21/0.57  fof(f897,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | (~spl1_1 | ~spl1_83)),
% 0.21/0.57    inference(resolution,[],[f882,f67])).
% 0.21/0.57  fof(f883,plain,(
% 0.21/0.57    spl1_83 | ~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_16 | ~spl1_71),
% 0.21/0.57    inference(avatar_split_clause,[],[f872,f737,f139,f84,f79,f75,f881])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    spl1_3 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    spl1_5 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.57  fof(f737,plain,(
% 0.21/0.57    spl1_71 <=> ! [X1,X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_71])])).
% 0.21/0.57  fof(f872,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_5 | ~spl1_16 | ~spl1_71)),
% 0.21/0.57    inference(forward_demodulation,[],[f871,f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f79])).
% 0.21/0.57  fof(f871,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) ) | (~spl1_3 | ~spl1_5 | ~spl1_16 | ~spl1_71)),
% 0.21/0.57    inference(subsumption_resolution,[],[f870,f141])).
% 0.21/0.57  fof(f870,plain,(
% 0.21/0.57    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_5 | ~spl1_71)),
% 0.21/0.57    inference(subsumption_resolution,[],[f868,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f75])).
% 0.21/0.57  fof(f868,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_5 | ~spl1_71)),
% 0.21/0.57    inference(superposition,[],[f738,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f84])).
% 0.21/0.57  fof(f738,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl1_71),
% 0.21/0.57    inference(avatar_component_clause,[],[f737])).
% 0.21/0.57  fof(f797,plain,(
% 0.21/0.57    spl1_74 | ~spl1_16 | ~spl1_52 | ~spl1_73),
% 0.21/0.57    inference(avatar_split_clause,[],[f765,f747,f556,f139,f794])).
% 0.21/0.57  fof(f747,plain,(
% 0.21/0.57    spl1_73 <=> ! [X17] : (~v1_relat_1(X17) | k4_relat_1(k5_relat_1(sK0,X17)) = k5_relat_1(k4_relat_1(X17),k4_relat_1(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_73])])).
% 0.21/0.57  fof(f765,plain,(
% 0.21/0.57    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | (~spl1_16 | ~spl1_52 | ~spl1_73)),
% 0.21/0.57    inference(forward_demodulation,[],[f751,f558])).
% 0.21/0.57  fof(f751,plain,(
% 0.21/0.57    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) | (~spl1_16 | ~spl1_73)),
% 0.21/0.57    inference(resolution,[],[f748,f141])).
% 0.21/0.57  fof(f748,plain,(
% 0.21/0.57    ( ! [X17] : (~v1_relat_1(X17) | k4_relat_1(k5_relat_1(sK0,X17)) = k5_relat_1(k4_relat_1(X17),k4_relat_1(sK0))) ) | ~spl1_73),
% 0.21/0.57    inference(avatar_component_clause,[],[f747])).
% 0.21/0.57  fof(f749,plain,(
% 0.21/0.57    spl1_73 | ~spl1_1 | ~spl1_41),
% 0.21/0.57    inference(avatar_split_clause,[],[f641,f374,f65,f747])).
% 0.21/0.57  fof(f374,plain,(
% 0.21/0.57    spl1_41 <=> ! [X1,X0] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_41])])).
% 0.21/0.57  fof(f641,plain,(
% 0.21/0.57    ( ! [X17] : (~v1_relat_1(X17) | k4_relat_1(k5_relat_1(sK0,X17)) = k5_relat_1(k4_relat_1(X17),k4_relat_1(sK0))) ) | (~spl1_1 | ~spl1_41)),
% 0.21/0.57    inference(resolution,[],[f375,f67])).
% 0.21/0.57  fof(f375,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) ) | ~spl1_41),
% 0.21/0.57    inference(avatar_component_clause,[],[f374])).
% 0.21/0.57  fof(f739,plain,(
% 0.21/0.57    spl1_71),
% 0.21/0.57    inference(avatar_split_clause,[],[f51,f737])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 0.21/0.57  fof(f559,plain,(
% 0.21/0.57    spl1_52 | ~spl1_1 | ~spl1_26 | ~spl1_51),
% 0.21/0.57    inference(avatar_split_clause,[],[f536,f506,f213,f65,f556])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    spl1_26 <=> ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_26])])).
% 0.21/0.57  fof(f506,plain,(
% 0.21/0.57    spl1_51 <=> ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_51])])).
% 0.21/0.57  fof(f536,plain,(
% 0.21/0.57    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_1 | ~spl1_26 | ~spl1_51)),
% 0.21/0.57    inference(forward_demodulation,[],[f535,f214])).
% 0.21/0.57  fof(f214,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) ) | ~spl1_26),
% 0.21/0.57    inference(avatar_component_clause,[],[f213])).
% 0.21/0.57  fof(f535,plain,(
% 0.21/0.57    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0)) | (~spl1_1 | ~spl1_26 | ~spl1_51)),
% 0.21/0.57    inference(forward_demodulation,[],[f525,f214])).
% 0.21/0.57  fof(f525,plain,(
% 0.21/0.57    k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) | (~spl1_1 | ~spl1_51)),
% 0.21/0.57    inference(resolution,[],[f507,f67])).
% 0.21/0.57  fof(f507,plain,(
% 0.21/0.57    ( ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18))) ) | ~spl1_51),
% 0.21/0.57    inference(avatar_component_clause,[],[f506])).
% 0.21/0.57  fof(f508,plain,(
% 0.21/0.57    spl1_51 | ~spl1_1 | ~spl1_33),
% 0.21/0.57    inference(avatar_split_clause,[],[f479,f271,f65,f506])).
% 0.21/0.57  fof(f271,plain,(
% 0.21/0.57    spl1_33 <=> ! [X1,X0] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_33])])).
% 0.21/0.57  fof(f479,plain,(
% 0.21/0.57    ( ! [X18] : (~v1_relat_1(X18) | k4_relat_1(k6_subset_1(sK0,X18)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X18))) ) | (~spl1_1 | ~spl1_33)),
% 0.21/0.57    inference(resolution,[],[f272,f67])).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))) ) | ~spl1_33),
% 0.21/0.57    inference(avatar_component_clause,[],[f271])).
% 0.21/0.57  fof(f406,plain,(
% 0.21/0.57    ~spl1_1 | ~spl1_8 | spl1_45),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f405])).
% 0.21/0.57  fof(f405,plain,(
% 0.21/0.57    $false | (~spl1_1 | ~spl1_8 | spl1_45)),
% 0.21/0.57    inference(subsumption_resolution,[],[f403,f67])).
% 0.21/0.57  fof(f403,plain,(
% 0.21/0.57    ~v1_relat_1(sK0) | (~spl1_8 | spl1_45)),
% 0.21/0.57    inference(resolution,[],[f401,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl1_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    spl1_8 <=> ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.57  fof(f401,plain,(
% 0.21/0.57    ~v1_relat_1(k4_relat_1(sK0)) | spl1_45),
% 0.21/0.57    inference(avatar_component_clause,[],[f399])).
% 0.21/0.57  fof(f376,plain,(
% 0.21/0.57    spl1_41),
% 0.21/0.57    inference(avatar_split_clause,[],[f50,f374])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.57  fof(f298,plain,(
% 0.21/0.57    ~spl1_1 | ~spl1_16 | ~spl1_17 | spl1_35),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f297])).
% 0.21/0.57  fof(f297,plain,(
% 0.21/0.57    $false | (~spl1_1 | ~spl1_16 | ~spl1_17 | spl1_35)),
% 0.21/0.57    inference(subsumption_resolution,[],[f296,f67])).
% 0.21/0.57  fof(f296,plain,(
% 0.21/0.57    ~v1_relat_1(sK0) | (~spl1_16 | ~spl1_17 | spl1_35)),
% 0.21/0.57    inference(subsumption_resolution,[],[f294,f141])).
% 0.21/0.57  fof(f294,plain,(
% 0.21/0.57    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | (~spl1_17 | spl1_35)),
% 0.21/0.57    inference(resolution,[],[f288,f153])).
% 0.21/0.57  fof(f288,plain,(
% 0.21/0.57    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl1_35),
% 0.21/0.57    inference(avatar_component_clause,[],[f287])).
% 0.21/0.57  fof(f287,plain,(
% 0.21/0.57    spl1_35 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_35])])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    ~spl1_35 | ~spl1_8 | spl1_34),
% 0.21/0.57    inference(avatar_split_clause,[],[f291,f283,f97,f287])).
% 0.21/0.57  fof(f291,plain,(
% 0.21/0.57    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | (~spl1_8 | spl1_34)),
% 0.21/0.57    inference(resolution,[],[f285,f98])).
% 0.21/0.57  fof(f285,plain,(
% 0.21/0.57    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | spl1_34),
% 0.21/0.57    inference(avatar_component_clause,[],[f283])).
% 0.21/0.57  fof(f273,plain,(
% 0.21/0.57    spl1_33),
% 0.21/0.57    inference(avatar_split_clause,[],[f49,f271])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    spl1_30 | ~spl1_16 | ~spl1_28),
% 0.21/0.57    inference(avatar_split_clause,[],[f231,f227,f139,f243])).
% 0.21/0.57  fof(f227,plain,(
% 0.21/0.57    spl1_28 <=> ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.21/0.57  fof(f231,plain,(
% 0.21/0.57    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) | (~spl1_16 | ~spl1_28)),
% 0.21/0.57    inference(resolution,[],[f228,f141])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | ~spl1_28),
% 0.21/0.57    inference(avatar_component_clause,[],[f227])).
% 0.21/0.57  fof(f229,plain,(
% 0.21/0.57    spl1_28 | ~spl1_1 | ~spl1_27),
% 0.21/0.57    inference(avatar_split_clause,[],[f225,f217,f65,f227])).
% 0.21/0.57  fof(f217,plain,(
% 0.21/0.57    spl1_27 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.21/0.57  fof(f225,plain,(
% 0.21/0.57    ( ! [X9] : (~v1_relat_1(X9) | k5_relat_1(sK0,X9) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X9)))) ) | (~spl1_1 | ~spl1_27)),
% 0.21/0.57    inference(resolution,[],[f218,f67])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | ~spl1_27),
% 0.21/0.57    inference(avatar_component_clause,[],[f217])).
% 0.21/0.57  fof(f219,plain,(
% 0.21/0.57    spl1_27 | ~spl1_10 | ~spl1_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f159,f152,f106,f217])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    spl1_10 <=> ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) ) | (~spl1_10 | ~spl1_17)),
% 0.21/0.57    inference(resolution,[],[f153,f107])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) ) | ~spl1_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f106])).
% 0.21/0.57  fof(f215,plain,(
% 0.21/0.57    spl1_26 | ~spl1_9 | ~spl1_18 | ~spl1_23),
% 0.21/0.57    inference(avatar_split_clause,[],[f210,f185,f156,f101,f213])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    spl1_9 <=> ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    spl1_18 <=> ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    spl1_23 <=> ! [X1,X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_23])])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) ) | (~spl1_9 | ~spl1_18 | ~spl1_23)),
% 0.21/0.57    inference(forward_demodulation,[],[f208,f102])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) ) | ~spl1_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f101])).
% 0.21/0.57  fof(f208,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) ) | (~spl1_18 | ~spl1_23)),
% 0.21/0.57    inference(superposition,[],[f186,f157])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) ) | ~spl1_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f156])).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) ) | ~spl1_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f185])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    spl1_23),
% 0.21/0.57    inference(avatar_split_clause,[],[f63,f185])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f56,f53,f53,f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f54,f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f55,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    ~spl1_19 | ~spl1_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f38,f165,f161])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.57    inference(negated_conjecture,[],[f20])).
% 0.21/0.57  fof(f20,conjecture,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    spl1_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f61,f156])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f43,f60])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    spl1_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f57,f152])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    ~spl1_2 | ~spl1_6 | spl1_16),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f147])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    $false | (~spl1_2 | ~spl1_6 | spl1_16)),
% 0.21/0.57    inference(subsumption_resolution,[],[f146,f72])).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0) | (~spl1_6 | spl1_16)),
% 0.21/0.57    inference(resolution,[],[f140,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) ) | ~spl1_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f89])).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    spl1_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ~v1_relat_1(k1_xboole_0) | spl1_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f139])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    spl1_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f52,f110])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.58    inference(flattening,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    spl1_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f48,f106])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.58  fof(f103,plain,(
% 0.21/0.58    spl1_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f62,f101])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(definition_unfolding,[],[f44,f53])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    spl1_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f47,f97])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    spl1_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f46,f93])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    spl1_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f45,f89])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    spl1_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f41,f84])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,axiom,(
% 0.21/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    spl1_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f40,f79])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    spl1_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f42,f75])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    spl1_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f39,f70])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    v1_xboole_0(k1_xboole_0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    spl1_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f37,f65])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    v1_relat_1(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f36])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (20749)------------------------------
% 0.21/0.58  % (20749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (20749)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (20749)Memory used [KB]: 6780
% 0.21/0.58  % (20749)Time elapsed: 0.145 s
% 0.21/0.58  % (20749)------------------------------
% 0.21/0.58  % (20749)------------------------------
% 0.21/0.58  % (20741)Success in time 0.218 s
%------------------------------------------------------------------------------
