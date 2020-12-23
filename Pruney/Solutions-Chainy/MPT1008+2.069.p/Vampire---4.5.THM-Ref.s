%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:18 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  271 ( 603 expanded)
%              Number of leaves         :   69 ( 263 expanded)
%              Depth                    :    9
%              Number of atoms          :  853 (1571 expanded)
%              Number of equality atoms :  210 ( 463 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f161,f166,f171,f176,f181,f186,f191,f197,f208,f213,f218,f232,f240,f255,f258,f304,f339,f345,f394,f490,f718,f955,f1003,f1032,f1039,f1066,f1082,f1084,f1378,f1387,f1463,f1595,f1740,f1749,f1763,f1848,f1852,f1964,f1983,f2119,f2124,f2352])).

fof(f2352,plain,
    ( spl8_42
    | ~ spl8_52
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f2351,f1103,f569,f487])).

fof(f487,plain,
    ( spl8_42
  <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f569,plain,
    ( spl8_52
  <=> ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f1103,plain,
    ( spl8_76
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f2351,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl8_52
    | ~ spl8_76 ),
    inference(trivial_inequality_removal,[],[f2350])).

fof(f2350,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | ~ spl8_52
    | ~ spl8_76 ),
    inference(superposition,[],[f570,f1105])).

fof(f1105,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f570,plain,
    ( ! [X0] :
        ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) )
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f569])).

fof(f2124,plain,
    ( spl8_75
    | spl8_76
    | ~ spl8_9
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f2123,f322,f194,f1103,f1099])).

fof(f1099,plain,
    ( spl8_75
  <=> o_0_0_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f194,plain,
    ( spl8_9
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f322,plain,
    ( spl8_24
  <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f2123,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl8_9
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f2120])).

fof(f2120,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)
    | o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl8_9
    | ~ spl8_24 ),
    inference(resolution,[],[f324,f1080])).

fof(f1080,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
        | k2_enumset1(X0,X0,X0,X0) = X3
        | k2_enumset1(X1,X1,X1,X1) = X3
        | k2_enumset1(X2,X2,X2,X2) = X3
        | k2_enumset1(X0,X0,X0,X1) = X3
        | k2_enumset1(X1,X1,X1,X2) = X3
        | k2_enumset1(X0,X0,X0,X2) = X3
        | k2_enumset1(X0,X0,X1,X2) = X3
        | o_0_0_xboole_0 = X3 )
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f129,f196])).

fof(f196,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X0,X0,X1,X2) = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f104,f114,f114,f114,f113,f113,f113,f93,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f113,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f84,f93])).

fof(f84,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f114,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f113])).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X3
      | k1_tarski(X0) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X2) = X3
      | k2_tarski(X0,X1) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k1_enumset1(X0,X1,X2) = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f324,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f322])).

fof(f2119,plain,
    ( spl8_24
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f2118,f301,f322])).

fof(f301,plain,
    ( spl8_20
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

% (5245)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f2118,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_20 ),
    inference(resolution,[],[f303,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f303,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f301])).

fof(f1983,plain,
    ( sK2 != k9_relat_1(sK2,o_0_0_xboole_0)
    | o_0_0_xboole_0 != k9_relat_1(sK2,o_0_0_xboole_0)
    | o_0_0_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1964,plain,
    ( ~ spl8_51
    | ~ spl8_118 ),
    inference(avatar_contradiction_clause,[],[f1957])).

fof(f1957,plain,
    ( $false
    | ~ spl8_51
    | ~ spl8_118 ),
    inference(resolution,[],[f1762,f563])).

fof(f563,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl8_51
  <=> ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f1762,plain,
    ( r2_hidden(sK3(sK2,o_0_0_xboole_0,sK2),o_0_0_xboole_0)
    | ~ spl8_118 ),
    inference(avatar_component_clause,[],[f1760])).

fof(f1760,plain,
    ( spl8_118
  <=> r2_hidden(sK3(sK2,o_0_0_xboole_0,sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f1852,plain,
    ( ~ spl8_25
    | ~ spl8_51
    | ~ spl8_75
    | ~ spl8_88
    | ~ spl8_110 ),
    inference(avatar_contradiction_clause,[],[f1850])).

fof(f1850,plain,
    ( $false
    | ~ spl8_25
    | ~ spl8_51
    | ~ spl8_75
    | ~ spl8_88
    | ~ spl8_110 ),
    inference(resolution,[],[f1527,f1594])).

fof(f1594,plain,
    ( r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2))
    | ~ spl8_110 ),
    inference(avatar_component_clause,[],[f1592])).

fof(f1592,plain,
    ( spl8_110
  <=> r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f1527,plain,
    ( ! [X3] : ~ r2_hidden(o_0_0_xboole_0,X3)
    | ~ spl8_25
    | ~ spl8_51
    | ~ spl8_75
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f1275,f1498])).

fof(f1498,plain,
    ( ! [X0] : o_0_0_xboole_0 = k1_funct_1(sK2,X0)
    | ~ spl8_25
    | ~ spl8_51
    | ~ spl8_75 ),
    inference(resolution,[],[f1265,f563])).

fof(f1265,plain,
    ( ! [X0] :
        ( r2_hidden(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(sK2,X0) )
    | ~ spl8_25
    | ~ spl8_75 ),
    inference(backward_demodulation,[],[f338,f1101])).

fof(f1101,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK2)
    | ~ spl8_75 ),
    inference(avatar_component_clause,[],[f1099])).

fof(f338,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_relat_1(sK2))
        | o_0_0_xboole_0 = k1_funct_1(sK2,X0) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl8_25
  <=> ! [X0] :
        ( o_0_0_xboole_0 = k1_funct_1(sK2,X0)
        | r2_hidden(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f1275,plain,
    ( ! [X3] : ~ r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3)
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f1274,plain,
    ( spl8_88
  <=> ! [X3] : ~ r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f1848,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k9_relat_1(sK2,o_0_0_xboole_0)
    | o_0_0_xboole_0 != k9_relat_1(sK2,o_0_0_xboole_0)
    | o_0_0_xboole_0 != k1_relat_1(sK2)
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1763,plain,
    ( spl8_118
    | spl8_117
    | ~ spl8_40
    | ~ spl8_51
    | ~ spl8_89 ),
    inference(avatar_split_clause,[],[f1734,f1277,f562,f475,f1755,f1760])).

fof(f1755,plain,
    ( spl8_117
  <=> sK2 = k9_relat_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f475,plain,
    ( spl8_40
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(sK2,X0,X1),X0)
        | k9_relat_1(sK2,X0) = X1
        | r2_hidden(sK3(sK2,X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f1277,plain,
    ( spl8_89
  <=> m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f1734,plain,
    ( sK2 = k9_relat_1(sK2,o_0_0_xboole_0)
    | r2_hidden(sK3(sK2,o_0_0_xboole_0,sK2),o_0_0_xboole_0)
    | ~ spl8_40
    | ~ spl8_51
    | ~ spl8_89 ),
    inference(resolution,[],[f1682,f1473])).

fof(f1473,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,sK2)
        | r2_hidden(X6,o_0_0_xboole_0) )
    | ~ spl8_89 ),
    inference(resolution,[],[f1279,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f1279,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1682,plain,
    ( ! [X12] :
        ( r2_hidden(sK3(sK2,o_0_0_xboole_0,X12),X12)
        | k9_relat_1(sK2,o_0_0_xboole_0) = X12 )
    | ~ spl8_40
    | ~ spl8_51 ),
    inference(resolution,[],[f476,f563])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK2,X0,X1),X0)
        | r2_hidden(sK3(sK2,X0,X1),X1)
        | k9_relat_1(sK2,X0) = X1 )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f475])).

fof(f1749,plain,
    ( spl8_115
    | ~ spl8_40
    | ~ spl8_51
    | ~ spl8_109 ),
    inference(avatar_split_clause,[],[f1726,f1589,f562,f475,f1746])).

fof(f1746,plain,
    ( spl8_115
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k9_relat_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f1589,plain,
    ( spl8_109
  <=> ! [X3] : ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f1726,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k9_relat_1(sK2,o_0_0_xboole_0)
    | ~ spl8_40
    | ~ spl8_51
    | ~ spl8_109 ),
    inference(resolution,[],[f1682,f1590])).

fof(f1590,plain,
    ( ! [X3] : ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl8_109 ),
    inference(avatar_component_clause,[],[f1589])).

fof(f1740,plain,
    ( spl8_113
    | ~ spl8_40
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f1724,f562,f475,f1737])).

fof(f1737,plain,
    ( spl8_113
  <=> o_0_0_xboole_0 = k9_relat_1(sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f1724,plain,
    ( o_0_0_xboole_0 = k9_relat_1(sK2,o_0_0_xboole_0)
    | ~ spl8_40
    | ~ spl8_51 ),
    inference(resolution,[],[f1682,f563])).

fof(f1595,plain,
    ( spl8_109
    | spl8_110
    | ~ spl8_25
    | ~ spl8_49
    | ~ spl8_51
    | ~ spl8_75 ),
    inference(avatar_split_clause,[],[f1587,f1099,f562,f554,f337,f1592,f1589])).

fof(f554,plain,
    ( spl8_49
  <=> ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),k2_relat_1(sK2))
        | ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f1587,plain,
    ( ! [X3] :
        ( r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2))
        | ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | ~ spl8_25
    | ~ spl8_49
    | ~ spl8_51
    | ~ spl8_75 ),
    inference(forward_demodulation,[],[f555,f1498])).

fof(f555,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),k2_relat_1(sK2))
        | ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f554])).

fof(f1463,plain,
    ( ~ spl8_14
    | ~ spl8_5
    | spl8_88
    | spl8_89
    | ~ spl8_9
    | ~ spl8_75 ),
    inference(avatar_split_clause,[],[f1462,f1099,f194,f1277,f1274,f173,f237])).

fof(f237,plain,
    ( spl8_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f173,plain,
    ( spl8_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1462,plain,
    ( ! [X3] :
        ( m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_9
    | ~ spl8_75 ),
    inference(forward_demodulation,[],[f1458,f220])).

fof(f220,plain,
    ( ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1)
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f139,f196])).

fof(f139,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1458,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X3))) )
    | ~ spl8_75 ),
    inference(superposition,[],[f142,f1101])).

fof(f142,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f1387,plain,
    ( spl8_18
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f1364,f163,f280])).

fof(f280,plain,
    ( spl8_18
  <=> k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f163,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1364,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f165,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f165,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f1378,plain,
    ( spl8_19
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f1363,f163,f290])).

fof(f290,plain,
    ( spl8_19
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f1363,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f165,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

% (5260)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1084,plain,
    ( spl8_50
    | spl8_51
    | ~ spl8_9
    | ~ spl8_31
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f557,f545,f392,f194,f562,f559])).

fof(f559,plain,
    ( spl8_50
  <=> ! [X1] : o_0_0_xboole_0 = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f392,plain,
    ( spl8_31
  <=> ! [X3] :
        ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X3)
        | r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f545,plain,
    ( spl8_47
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_2(o_0_0_xboole_0,X0,X1)
        | ~ r2_hidden(X2,X0)
        | o_0_0_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f557,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X1 )
    | ~ spl8_9
    | ~ spl8_31
    | ~ spl8_47 ),
    inference(resolution,[],[f546,f465])).

fof(f465,plain,
    ( ! [X0] : v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X0)
    | ~ spl8_9
    | ~ spl8_31 ),
    inference(resolution,[],[f408,f202])).

fof(f202,plain,
    ( ! [X0] : r1_tarski(o_0_0_xboole_0,X0)
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f63,f196])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f408,plain,
    ( ! [X6] :
        ( ~ r1_tarski(o_0_0_xboole_0,sK7(o_0_0_xboole_0,X6,o_0_0_xboole_0))
        | v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X6) )
    | ~ spl8_31 ),
    inference(resolution,[],[f393,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f393,plain,
    ( ! [X3] :
        ( r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0)
        | v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X3) )
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f392])).

fof(f546,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(o_0_0_xboole_0,X0,X1)
        | ~ r2_hidden(X2,X0)
        | o_0_0_xboole_0 = X1 )
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f545])).

fof(f1082,plain,
    ( ~ spl8_9
    | spl8_57 ),
    inference(avatar_contradiction_clause,[],[f1081])).

fof(f1081,plain,
    ( $false
    | ~ spl8_9
    | spl8_57 ),
    inference(resolution,[],[f605,f202])).

fof(f605,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | spl8_57 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl8_57
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f1066,plain,
    ( ~ spl8_57
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f1063,f548,f603])).

fof(f548,plain,
    ( spl8_48
  <=> r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f1063,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl8_48 ),
    inference(resolution,[],[f550,f92])).

fof(f550,plain,
    ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f548])).

fof(f1039,plain,
    ( spl8_47
    | ~ spl8_16
    | spl8_48
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f1038,f343,f210,f194,f548,f249,f545])).

fof(f249,plain,
    ( spl8_16
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f210,plain,
    ( spl8_11
  <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f343,plain,
    ( spl8_26
  <=> ! [X3] :
        ( r2_hidden(X3,o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f1038,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)
        | ~ v1_funct_1(o_0_0_xboole_0)
        | ~ v1_funct_2(o_0_0_xboole_0,X0,X1)
        | o_0_0_xboole_0 = X1
        | ~ r2_hidden(X2,X0) )
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f1037,f355])).

fof(f355,plain,
    ( ! [X0] : o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)
    | ~ spl8_9
    | ~ spl8_26 ),
    inference(resolution,[],[f349,f202])).

fof(f349,plain,
    ( ! [X5] :
        ( ~ r1_tarski(o_0_0_xboole_0,X5)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X5) )
    | ~ spl8_26 ),
    inference(resolution,[],[f344,f92])).

fof(f344,plain,
    ( ! [X3] :
        ( r2_hidden(X3,o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f343])).

fof(f1037,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_funct_1(o_0_0_xboole_0,X2),o_0_0_xboole_0)
        | ~ v1_funct_1(o_0_0_xboole_0)
        | ~ v1_funct_2(o_0_0_xboole_0,X0,X1)
        | o_0_0_xboole_0 = X1
        | ~ r2_hidden(X2,X0) )
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f998,f288])).

fof(f288,plain,
    ( ! [X0,X1] : o_0_0_xboole_0 = k2_relset_1(X0,X1,o_0_0_xboole_0)
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f284,f212])).

fof(f212,plain,
    ( o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f210])).

fof(f284,plain,
    ( ! [X0,X1] : k2_relat_1(o_0_0_xboole_0) = k2_relset_1(X0,X1,o_0_0_xboole_0)
    | ~ spl8_9 ),
    inference(resolution,[],[f96,f201])).

fof(f201,plain,
    ( ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f64,f196])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f998,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(o_0_0_xboole_0)
        | ~ v1_funct_2(o_0_0_xboole_0,X0,X1)
        | o_0_0_xboole_0 = X1
        | ~ r2_hidden(X2,X0)
        | r2_hidden(k1_funct_1(o_0_0_xboole_0,X2),k2_relset_1(X0,X1,o_0_0_xboole_0)) )
    | ~ spl8_9 ),
    inference(resolution,[],[f531,f201])).

fof(f531,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | o_0_0_xboole_0 = X1
        | ~ r2_hidden(X2,X0)
        | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) )
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f103,f196])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f1032,plain,
    ( spl8_52
    | ~ spl8_14
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1029,f173,f237,f569])).

fof(f1029,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK2)
        | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(sK2)
        | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f120,f175])).

fof(f175,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0)
      | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) ) ),
    inference(definition_unfolding,[],[f86,f114,f114])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f1003,plain,
    ( spl8_12
    | ~ spl8_4
    | ~ spl8_5
    | spl8_49
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1002,f290,f194,f163,f554,f173,f168,f215])).

fof(f215,plain,
    ( spl8_12
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f168,plain,
    ( spl8_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1002,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | o_0_0_xboole_0 = sK1
        | ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0)) )
    | ~ spl8_3
    | ~ spl8_9
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f999,f292])).

fof(f292,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f290])).

fof(f999,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
        | o_0_0_xboole_0 = sK1
        | ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(k1_funct_1(sK2,X3),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)) )
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(resolution,[],[f531,f165])).

fof(f955,plain,
    ( spl8_40
    | ~ spl8_14
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f952,f173,f237,f475])).

fof(f952,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK2)
        | r2_hidden(sK5(sK2,X2,X3),X2)
        | r2_hidden(sK3(sK2,X2,X3),X3)
        | k9_relat_1(sK2,X2) = X3 )
    | ~ spl8_5 ),
    inference(resolution,[],[f74,f175])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f718,plain,
    ( ~ spl8_6
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f627,f559,f178])).

fof(f178,plain,
    ( spl8_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f627,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_50 ),
    inference(backward_demodulation,[],[f118,f560])).

fof(f560,plain,
    ( ! [X1] : o_0_0_xboole_0 = X1
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f559])).

fof(f118,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f62,f114])).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f490,plain,
    ( ~ spl8_42
    | spl8_1
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f485,f290,f153,f487])).

fof(f153,plain,
    ( spl8_1
  <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f485,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | spl8_1
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f155,f292])).

fof(f155,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f153])).

fof(f394,plain,
    ( ~ spl8_13
    | spl8_31
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f390,f249,f205,f392,f229])).

fof(f229,plain,
    ( spl8_13
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f205,plain,
    ( spl8_10
  <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f390,plain,
    ( ! [X3] :
        ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X3)
        | r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0)
        | ~ v1_relat_1(o_0_0_xboole_0) )
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f389,f207])).

fof(f207,plain,
    ( o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f389,plain,
    ( ! [X3] :
        ( r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0)
        | ~ v1_relat_1(o_0_0_xboole_0)
        | v1_funct_2(o_0_0_xboole_0,k1_relat_1(o_0_0_xboole_0),X3) )
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f381,f207])).

fof(f381,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(o_0_0_xboole_0)
        | r2_hidden(sK7(k1_relat_1(o_0_0_xboole_0),X3,o_0_0_xboole_0),k1_relat_1(o_0_0_xboole_0))
        | v1_funct_2(o_0_0_xboole_0,k1_relat_1(o_0_0_xboole_0),X3) )
    | ~ spl8_16 ),
    inference(resolution,[],[f141,f251])).

fof(f251,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f249])).

fof(f141,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | v1_funct_2(X2,k1_relat_1(X2),X1) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK7(X0,X1,X2),X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f345,plain,
    ( ~ spl8_13
    | spl8_26
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f341,f249,f205,f194,f343,f229])).

fof(f341,plain,
    ( ! [X3] :
        ( r2_hidden(X3,o_0_0_xboole_0)
        | ~ v1_relat_1(o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3) )
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f335,f207])).

fof(f335,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(o_0_0_xboole_0)
        | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3)
        | r2_hidden(X3,k1_relat_1(o_0_0_xboole_0)) )
    | ~ spl8_9
    | ~ spl8_16 ),
    inference(resolution,[],[f327,f251])).

fof(f327,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | o_0_0_xboole_0 = k1_funct_1(X0,X1)
        | r2_hidden(X1,k1_relat_1(X0)) )
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f131,f196])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = k1_funct_1(X0,X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

% (5256)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f339,plain,
    ( spl8_25
    | ~ spl8_14
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f333,f194,f173,f237,f337])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | o_0_0_xboole_0 = k1_funct_1(sK2,X0)
        | r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_5
    | ~ spl8_9 ),
    inference(resolution,[],[f327,f175])).

fof(f304,plain,
    ( spl8_20
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f299,f280,f163,f301])).

fof(f299,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f295,f282])).

fof(f282,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f280])).

fof(f295,plain,
    ( m1_subset_1(k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl8_3 ),
    inference(resolution,[],[f97,f165])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f258,plain,
    ( ~ spl8_14
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f256,f253,f173,f237])).

fof(f253,plain,
    ( spl8_17
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f256,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl8_5
    | ~ spl8_17 ),
    inference(resolution,[],[f254,f175])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl8_16
    | spl8_17
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f246,f194,f253,f249])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | v1_funct_1(o_0_0_xboole_0) )
    | ~ spl8_9 ),
    inference(resolution,[],[f67,f201])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f240,plain,
    ( spl8_14
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f234,f163,f237])).

fof(f234,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f165,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f232,plain,
    ( spl8_13
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f225,f194,f229])).

fof(f225,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl8_9 ),
    inference(resolution,[],[f94,f201])).

fof(f218,plain,
    ( ~ spl8_12
    | spl8_2
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f203,f194,f158,f215])).

fof(f158,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f203,plain,
    ( o_0_0_xboole_0 != sK1
    | spl8_2
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f160,f196])).

fof(f160,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f213,plain,
    ( spl8_11
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f200,f194,f183,f210])).

fof(f183,plain,
    ( spl8_7
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f200,plain,
    ( o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f185,f196])).

fof(f185,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f183])).

fof(f208,plain,
    ( spl8_10
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f199,f194,f188,f205])).

fof(f188,plain,
    ( spl8_8
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f199,plain,
    ( o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | ~ spl8_8
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f190,f196])).

fof(f190,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f197,plain,
    ( spl8_9
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f192,f178,f194])).

fof(f192,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_6 ),
    inference(resolution,[],[f66,f180])).

fof(f180,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f178])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f191,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f60,f188])).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f186,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f61,f183])).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f181,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f59,f178])).

fof(f59,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f176,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f54,f173])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

fof(f171,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f117,f168])).

fof(f117,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f55,f114])).

fof(f55,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f166,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f116,f163])).

fof(f116,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f56,f114])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f161,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f57,f158])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f156,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f115,f153])).

fof(f115,plain,(
    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) ),
    inference(definition_unfolding,[],[f58,f114,f114])).

fof(f58,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (5240)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.49  % (5248)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (5254)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (5246)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.09/0.51  % (5238)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.09/0.52  % (5234)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.09/0.52  % (5242)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.09/0.52  % (5235)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.09/0.52  % (5236)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.09/0.52  % (5241)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (5261)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.53  % (5250)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.53  % (5251)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.28/0.54  % (5237)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (5253)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.54  % (5249)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.54  % (5243)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (5244)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (5233)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (5258)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (5259)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.55  % (5239)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.55  % (5232)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.28/0.55  % (5257)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.56  % (5255)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.56  % (5249)Refutation not found, incomplete strategy% (5249)------------------------------
% 1.28/0.56  % (5249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.56  % (5249)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.56  
% 1.28/0.56  % (5249)Memory used [KB]: 10746
% 1.28/0.56  % (5249)Time elapsed: 0.153 s
% 1.28/0.56  % (5249)------------------------------
% 1.28/0.56  % (5249)------------------------------
% 1.28/0.56  % (5248)Refutation found. Thanks to Tanya!
% 1.28/0.56  % SZS status Theorem for theBenchmark
% 1.28/0.56  % (5247)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.56  % SZS output start Proof for theBenchmark
% 1.28/0.56  fof(f2353,plain,(
% 1.28/0.56    $false),
% 1.28/0.56    inference(avatar_sat_refutation,[],[f156,f161,f166,f171,f176,f181,f186,f191,f197,f208,f213,f218,f232,f240,f255,f258,f304,f339,f345,f394,f490,f718,f955,f1003,f1032,f1039,f1066,f1082,f1084,f1378,f1387,f1463,f1595,f1740,f1749,f1763,f1848,f1852,f1964,f1983,f2119,f2124,f2352])).
% 1.28/0.56  fof(f2352,plain,(
% 1.28/0.56    spl8_42 | ~spl8_52 | ~spl8_76),
% 1.28/0.56    inference(avatar_split_clause,[],[f2351,f1103,f569,f487])).
% 1.28/0.56  fof(f487,plain,(
% 1.28/0.56    spl8_42 <=> k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.28/0.56  fof(f569,plain,(
% 1.28/0.56    spl8_52 <=> ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)))),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 1.28/0.56  fof(f1103,plain,(
% 1.28/0.56    spl8_76 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).
% 1.28/0.56  fof(f2351,plain,(
% 1.28/0.56    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | (~spl8_52 | ~spl8_76)),
% 1.28/0.56    inference(trivial_inequality_removal,[],[f2350])).
% 1.28/0.56  fof(f2350,plain,(
% 1.28/0.56    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2) | (~spl8_52 | ~spl8_76)),
% 1.28/0.56    inference(superposition,[],[f570,f1105])).
% 1.28/0.56  fof(f1105,plain,(
% 1.28/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | ~spl8_76),
% 1.28/0.56    inference(avatar_component_clause,[],[f1103])).
% 1.28/0.56  fof(f570,plain,(
% 1.28/0.56    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0))) ) | ~spl8_52),
% 1.28/0.56    inference(avatar_component_clause,[],[f569])).
% 1.28/0.56  fof(f2124,plain,(
% 1.28/0.56    spl8_75 | spl8_76 | ~spl8_9 | ~spl8_24),
% 1.28/0.56    inference(avatar_split_clause,[],[f2123,f322,f194,f1103,f1099])).
% 1.28/0.56  fof(f1099,plain,(
% 1.28/0.56    spl8_75 <=> o_0_0_xboole_0 = k1_relat_1(sK2)),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).
% 1.28/0.56  fof(f194,plain,(
% 1.28/0.56    spl8_9 <=> o_0_0_xboole_0 = k1_xboole_0),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.28/0.56  fof(f322,plain,(
% 1.28/0.56    spl8_24 <=> r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.28/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.28/0.56  fof(f2123,plain,(
% 1.28/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2) | (~spl8_9 | ~spl8_24)),
% 1.28/0.56    inference(duplicate_literal_removal,[],[f2120])).
% 1.28/0.56  fof(f2120,plain,(
% 1.28/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2) | o_0_0_xboole_0 = k1_relat_1(sK2) | (~spl8_9 | ~spl8_24)),
% 1.28/0.56    inference(resolution,[],[f324,f1080])).
% 1.28/0.57  fof(f1080,plain,(
% 1.28/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k2_enumset1(X0,X0,X0,X0) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X0,X0,X1,X2) = X3 | o_0_0_xboole_0 = X3) ) | ~spl8_9),
% 1.28/0.57    inference(forward_demodulation,[],[f129,f196])).
% 1.28/0.57  fof(f196,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k1_xboole_0 | ~spl8_9),
% 1.28/0.57    inference(avatar_component_clause,[],[f194])).
% 1.28/0.57  fof(f129,plain,(
% 1.28/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X0,X0,X1,X2) = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 1.28/0.57    inference(definition_unfolding,[],[f104,f114,f114,f114,f113,f113,f113,f93,f93])).
% 1.28/0.57  fof(f93,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f6])).
% 1.28/0.57  fof(f6,axiom,(
% 1.28/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.28/0.57  fof(f113,plain,(
% 1.28/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.28/0.57    inference(definition_unfolding,[],[f84,f93])).
% 1.28/0.57  fof(f84,plain,(
% 1.28/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f5])).
% 1.28/0.57  fof(f5,axiom,(
% 1.28/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.57  fof(f114,plain,(
% 1.28/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.28/0.57    inference(definition_unfolding,[],[f65,f113])).
% 1.28/0.57  fof(f65,plain,(
% 1.28/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f4])).
% 1.28/0.57  fof(f4,axiom,(
% 1.28/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.28/0.57  fof(f104,plain,(
% 1.28/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X3 | k1_tarski(X0) = X3 | k1_tarski(X1) = X3 | k1_tarski(X2) = X3 | k2_tarski(X0,X1) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k1_enumset1(X0,X1,X2) = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.28/0.57    inference(cnf_transformation,[],[f53])).
% 1.28/0.57  fof(f53,plain,(
% 1.28/0.57    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.28/0.57    inference(ennf_transformation,[],[f9])).
% 1.28/0.57  fof(f9,axiom,(
% 1.28/0.57    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 1.28/0.57  fof(f324,plain,(
% 1.28/0.57    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_24),
% 1.28/0.57    inference(avatar_component_clause,[],[f322])).
% 1.28/0.57  fof(f2119,plain,(
% 1.28/0.57    spl8_24 | ~spl8_20),
% 1.28/0.57    inference(avatar_split_clause,[],[f2118,f301,f322])).
% 1.28/0.57  fof(f301,plain,(
% 1.28/0.57    spl8_20 <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.28/0.57  % (5245)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.57  fof(f2118,plain,(
% 1.28/0.57    r1_tarski(k1_relat_1(sK2),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl8_20),
% 1.28/0.57    inference(resolution,[],[f303,f88])).
% 1.28/0.57  fof(f88,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f12])).
% 1.28/0.57  fof(f12,axiom,(
% 1.28/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.28/0.57  fof(f303,plain,(
% 1.28/0.57    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl8_20),
% 1.28/0.57    inference(avatar_component_clause,[],[f301])).
% 1.28/0.57  fof(f1983,plain,(
% 1.28/0.57    sK2 != k9_relat_1(sK2,o_0_0_xboole_0) | o_0_0_xboole_0 != k9_relat_1(sK2,o_0_0_xboole_0) | o_0_0_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(k1_xboole_0) | r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0) | ~r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2))),
% 1.28/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.28/0.57  fof(f1964,plain,(
% 1.28/0.57    ~spl8_51 | ~spl8_118),
% 1.28/0.57    inference(avatar_contradiction_clause,[],[f1957])).
% 1.28/0.57  fof(f1957,plain,(
% 1.28/0.57    $false | (~spl8_51 | ~spl8_118)),
% 1.28/0.57    inference(resolution,[],[f1762,f563])).
% 1.28/0.57  fof(f563,plain,(
% 1.28/0.57    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) ) | ~spl8_51),
% 1.28/0.57    inference(avatar_component_clause,[],[f562])).
% 1.28/0.57  fof(f562,plain,(
% 1.28/0.57    spl8_51 <=> ! [X0] : ~r2_hidden(X0,o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.28/0.57  fof(f1762,plain,(
% 1.28/0.57    r2_hidden(sK3(sK2,o_0_0_xboole_0,sK2),o_0_0_xboole_0) | ~spl8_118),
% 1.28/0.57    inference(avatar_component_clause,[],[f1760])).
% 1.28/0.57  fof(f1760,plain,(
% 1.28/0.57    spl8_118 <=> r2_hidden(sK3(sK2,o_0_0_xboole_0,sK2),o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).
% 1.28/0.57  fof(f1852,plain,(
% 1.28/0.57    ~spl8_25 | ~spl8_51 | ~spl8_75 | ~spl8_88 | ~spl8_110),
% 1.28/0.57    inference(avatar_contradiction_clause,[],[f1850])).
% 1.28/0.57  fof(f1850,plain,(
% 1.28/0.57    $false | (~spl8_25 | ~spl8_51 | ~spl8_75 | ~spl8_88 | ~spl8_110)),
% 1.28/0.57    inference(resolution,[],[f1527,f1594])).
% 1.28/0.57  fof(f1594,plain,(
% 1.28/0.57    r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2)) | ~spl8_110),
% 1.28/0.57    inference(avatar_component_clause,[],[f1592])).
% 1.28/0.57  fof(f1592,plain,(
% 1.28/0.57    spl8_110 <=> r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).
% 1.28/0.57  fof(f1527,plain,(
% 1.28/0.57    ( ! [X3] : (~r2_hidden(o_0_0_xboole_0,X3)) ) | (~spl8_25 | ~spl8_51 | ~spl8_75 | ~spl8_88)),
% 1.28/0.57    inference(forward_demodulation,[],[f1275,f1498])).
% 1.28/0.57  fof(f1498,plain,(
% 1.28/0.57    ( ! [X0] : (o_0_0_xboole_0 = k1_funct_1(sK2,X0)) ) | (~spl8_25 | ~spl8_51 | ~spl8_75)),
% 1.28/0.57    inference(resolution,[],[f1265,f563])).
% 1.28/0.57  fof(f1265,plain,(
% 1.28/0.57    ( ! [X0] : (r2_hidden(X0,o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(sK2,X0)) ) | (~spl8_25 | ~spl8_75)),
% 1.28/0.57    inference(backward_demodulation,[],[f338,f1101])).
% 1.28/0.57  fof(f1101,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k1_relat_1(sK2) | ~spl8_75),
% 1.28/0.57    inference(avatar_component_clause,[],[f1099])).
% 1.28/0.57  fof(f338,plain,(
% 1.28/0.57    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK2)) | o_0_0_xboole_0 = k1_funct_1(sK2,X0)) ) | ~spl8_25),
% 1.28/0.57    inference(avatar_component_clause,[],[f337])).
% 1.28/0.57  fof(f337,plain,(
% 1.28/0.57    spl8_25 <=> ! [X0] : (o_0_0_xboole_0 = k1_funct_1(sK2,X0) | r2_hidden(X0,k1_relat_1(sK2)))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.28/0.57  fof(f1275,plain,(
% 1.28/0.57    ( ! [X3] : (~r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3)) ) | ~spl8_88),
% 1.28/0.57    inference(avatar_component_clause,[],[f1274])).
% 1.28/0.57  fof(f1274,plain,(
% 1.28/0.57    spl8_88 <=> ! [X3] : ~r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 1.28/0.57  fof(f1848,plain,(
% 1.28/0.57    k2_enumset1(sK0,sK0,sK0,sK0) != k9_relat_1(sK2,o_0_0_xboole_0) | o_0_0_xboole_0 != k9_relat_1(sK2,o_0_0_xboole_0) | o_0_0_xboole_0 != k1_relat_1(sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK2)),
% 1.28/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.28/0.57  fof(f1763,plain,(
% 1.28/0.57    spl8_118 | spl8_117 | ~spl8_40 | ~spl8_51 | ~spl8_89),
% 1.28/0.57    inference(avatar_split_clause,[],[f1734,f1277,f562,f475,f1755,f1760])).
% 1.28/0.57  fof(f1755,plain,(
% 1.28/0.57    spl8_117 <=> sK2 = k9_relat_1(sK2,o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).
% 1.28/0.57  fof(f475,plain,(
% 1.28/0.57    spl8_40 <=> ! [X1,X0] : (r2_hidden(sK5(sK2,X0,X1),X0) | k9_relat_1(sK2,X0) = X1 | r2_hidden(sK3(sK2,X0,X1),X1))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 1.28/0.57  fof(f1277,plain,(
% 1.28/0.57    spl8_89 <=> m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 1.28/0.57  fof(f1734,plain,(
% 1.28/0.57    sK2 = k9_relat_1(sK2,o_0_0_xboole_0) | r2_hidden(sK3(sK2,o_0_0_xboole_0,sK2),o_0_0_xboole_0) | (~spl8_40 | ~spl8_51 | ~spl8_89)),
% 1.28/0.57    inference(resolution,[],[f1682,f1473])).
% 1.28/0.57  fof(f1473,plain,(
% 1.28/0.57    ( ! [X6] : (~r2_hidden(X6,sK2) | r2_hidden(X6,o_0_0_xboole_0)) ) | ~spl8_89),
% 1.28/0.57    inference(resolution,[],[f1279,f85])).
% 1.28/0.57  fof(f85,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f39])).
% 1.28/0.57  fof(f39,plain,(
% 1.28/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.57    inference(ennf_transformation,[],[f10])).
% 1.28/0.57  fof(f10,axiom,(
% 1.28/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.28/0.57  fof(f1279,plain,(
% 1.28/0.57    m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) | ~spl8_89),
% 1.28/0.57    inference(avatar_component_clause,[],[f1277])).
% 1.28/0.57  fof(f1682,plain,(
% 1.28/0.57    ( ! [X12] : (r2_hidden(sK3(sK2,o_0_0_xboole_0,X12),X12) | k9_relat_1(sK2,o_0_0_xboole_0) = X12) ) | (~spl8_40 | ~spl8_51)),
% 1.28/0.57    inference(resolution,[],[f476,f563])).
% 1.28/0.57  fof(f476,plain,(
% 1.28/0.57    ( ! [X0,X1] : (r2_hidden(sK5(sK2,X0,X1),X0) | r2_hidden(sK3(sK2,X0,X1),X1) | k9_relat_1(sK2,X0) = X1) ) | ~spl8_40),
% 1.28/0.57    inference(avatar_component_clause,[],[f475])).
% 1.28/0.57  fof(f1749,plain,(
% 1.28/0.57    spl8_115 | ~spl8_40 | ~spl8_51 | ~spl8_109),
% 1.28/0.57    inference(avatar_split_clause,[],[f1726,f1589,f562,f475,f1746])).
% 1.28/0.57  fof(f1746,plain,(
% 1.28/0.57    spl8_115 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k9_relat_1(sK2,o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).
% 1.28/0.57  fof(f1589,plain,(
% 1.28/0.57    spl8_109 <=> ! [X3] : ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).
% 1.28/0.57  fof(f1726,plain,(
% 1.28/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k9_relat_1(sK2,o_0_0_xboole_0) | (~spl8_40 | ~spl8_51 | ~spl8_109)),
% 1.28/0.57    inference(resolution,[],[f1682,f1590])).
% 1.28/0.57  fof(f1590,plain,(
% 1.28/0.57    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl8_109),
% 1.28/0.57    inference(avatar_component_clause,[],[f1589])).
% 1.28/0.57  fof(f1740,plain,(
% 1.28/0.57    spl8_113 | ~spl8_40 | ~spl8_51),
% 1.28/0.57    inference(avatar_split_clause,[],[f1724,f562,f475,f1737])).
% 1.28/0.57  fof(f1737,plain,(
% 1.28/0.57    spl8_113 <=> o_0_0_xboole_0 = k9_relat_1(sK2,o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).
% 1.28/0.57  fof(f1724,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k9_relat_1(sK2,o_0_0_xboole_0) | (~spl8_40 | ~spl8_51)),
% 1.28/0.57    inference(resolution,[],[f1682,f563])).
% 1.28/0.57  fof(f1595,plain,(
% 1.28/0.57    spl8_109 | spl8_110 | ~spl8_25 | ~spl8_49 | ~spl8_51 | ~spl8_75),
% 1.28/0.57    inference(avatar_split_clause,[],[f1587,f1099,f562,f554,f337,f1592,f1589])).
% 1.28/0.57  fof(f554,plain,(
% 1.28/0.57    spl8_49 <=> ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),k2_relat_1(sK2)) | ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.28/0.57  fof(f1587,plain,(
% 1.28/0.57    ( ! [X3] : (r2_hidden(o_0_0_xboole_0,k2_relat_1(sK2)) | ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0))) ) | (~spl8_25 | ~spl8_49 | ~spl8_51 | ~spl8_75)),
% 1.28/0.57    inference(forward_demodulation,[],[f555,f1498])).
% 1.28/0.57  fof(f555,plain,(
% 1.28/0.57    ( ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),k2_relat_1(sK2)) | ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0))) ) | ~spl8_49),
% 1.28/0.57    inference(avatar_component_clause,[],[f554])).
% 1.28/0.57  fof(f1463,plain,(
% 1.28/0.57    ~spl8_14 | ~spl8_5 | spl8_88 | spl8_89 | ~spl8_9 | ~spl8_75),
% 1.28/0.57    inference(avatar_split_clause,[],[f1462,f1099,f194,f1277,f1274,f173,f237])).
% 1.28/0.57  fof(f237,plain,(
% 1.28/0.57    spl8_14 <=> v1_relat_1(sK2)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.28/0.57  fof(f173,plain,(
% 1.28/0.57    spl8_5 <=> v1_funct_1(sK2)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.28/0.57  fof(f1462,plain,(
% 1.28/0.57    ( ! [X3] : (m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) | ~r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl8_9 | ~spl8_75)),
% 1.28/0.57    inference(forward_demodulation,[],[f1458,f220])).
% 1.28/0.57  fof(f220,plain,(
% 1.28/0.57    ( ! [X1] : (o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1)) ) | ~spl8_9),
% 1.28/0.57    inference(forward_demodulation,[],[f139,f196])).
% 1.28/0.57  fof(f139,plain,(
% 1.28/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.28/0.57    inference(equality_resolution,[],[f90])).
% 1.28/0.57  fof(f90,plain,(
% 1.28/0.57    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f8])).
% 1.28/0.57  fof(f8,axiom,(
% 1.28/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.28/0.57  fof(f1458,plain,(
% 1.28/0.57    ( ! [X3] : (~r2_hidden(k1_funct_1(sK2,sK7(o_0_0_xboole_0,X3,sK2)),X3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X3)))) ) | ~spl8_75),
% 1.28/0.57    inference(superposition,[],[f142,f1101])).
% 1.28/0.57  fof(f142,plain,(
% 1.28/0.57    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 1.28/0.57    inference(equality_resolution,[],[f99])).
% 1.28/0.57  fof(f99,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | ~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.57    inference(cnf_transformation,[],[f48])).
% 1.28/0.57  fof(f48,plain,(
% 1.28/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.28/0.57    inference(flattening,[],[f47])).
% 1.28/0.57  fof(f47,plain,(
% 1.28/0.57    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.28/0.57    inference(ennf_transformation,[],[f25])).
% 1.28/0.57  fof(f25,axiom,(
% 1.28/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 1.28/0.57  fof(f1387,plain,(
% 1.28/0.57    spl8_18 | ~spl8_3),
% 1.28/0.57    inference(avatar_split_clause,[],[f1364,f163,f280])).
% 1.28/0.57  fof(f280,plain,(
% 1.28/0.57    spl8_18 <=> k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.28/0.57  fof(f163,plain,(
% 1.28/0.57    spl8_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.28/0.57  fof(f1364,plain,(
% 1.28/0.57    k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) | ~spl8_3),
% 1.28/0.57    inference(resolution,[],[f165,f95])).
% 1.28/0.57  fof(f95,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f44])).
% 1.28/0.57  fof(f44,plain,(
% 1.28/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.57    inference(ennf_transformation,[],[f22])).
% 1.28/0.57  fof(f22,axiom,(
% 1.28/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.28/0.57  fof(f165,plain,(
% 1.28/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl8_3),
% 1.28/0.57    inference(avatar_component_clause,[],[f163])).
% 1.28/0.57  fof(f1378,plain,(
% 1.28/0.57    spl8_19 | ~spl8_3),
% 1.28/0.57    inference(avatar_split_clause,[],[f1363,f163,f290])).
% 1.28/0.57  fof(f290,plain,(
% 1.28/0.57    spl8_19 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.28/0.57  fof(f1363,plain,(
% 1.28/0.57    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl8_3),
% 1.28/0.57    inference(resolution,[],[f165,f96])).
% 1.28/0.57  fof(f96,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f45])).
% 1.28/0.57  fof(f45,plain,(
% 1.28/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.57    inference(ennf_transformation,[],[f23])).
% 1.28/0.57  % (5260)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.57  fof(f23,axiom,(
% 1.28/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.28/0.57  fof(f1084,plain,(
% 1.28/0.57    spl8_50 | spl8_51 | ~spl8_9 | ~spl8_31 | ~spl8_47),
% 1.28/0.57    inference(avatar_split_clause,[],[f557,f545,f392,f194,f562,f559])).
% 1.28/0.57  fof(f559,plain,(
% 1.28/0.57    spl8_50 <=> ! [X1] : o_0_0_xboole_0 = X1),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 1.28/0.57  fof(f392,plain,(
% 1.28/0.57    spl8_31 <=> ! [X3] : (v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X3) | r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.28/0.57  fof(f545,plain,(
% 1.28/0.57    spl8_47 <=> ! [X1,X0,X2] : (~v1_funct_2(o_0_0_xboole_0,X0,X1) | ~r2_hidden(X2,X0) | o_0_0_xboole_0 = X1)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 1.28/0.57  fof(f557,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~r2_hidden(X0,o_0_0_xboole_0) | o_0_0_xboole_0 = X1) ) | (~spl8_9 | ~spl8_31 | ~spl8_47)),
% 1.28/0.57    inference(resolution,[],[f546,f465])).
% 1.28/0.57  fof(f465,plain,(
% 1.28/0.57    ( ! [X0] : (v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X0)) ) | (~spl8_9 | ~spl8_31)),
% 1.28/0.57    inference(resolution,[],[f408,f202])).
% 1.28/0.57  fof(f202,plain,(
% 1.28/0.57    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) ) | ~spl8_9),
% 1.28/0.57    inference(backward_demodulation,[],[f63,f196])).
% 1.28/0.57  fof(f63,plain,(
% 1.28/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f3])).
% 1.28/0.57  fof(f3,axiom,(
% 1.28/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.28/0.57  fof(f408,plain,(
% 1.28/0.57    ( ! [X6] : (~r1_tarski(o_0_0_xboole_0,sK7(o_0_0_xboole_0,X6,o_0_0_xboole_0)) | v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X6)) ) | ~spl8_31),
% 1.28/0.57    inference(resolution,[],[f393,f92])).
% 1.28/0.57  fof(f92,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f42])).
% 1.28/0.57  fof(f42,plain,(
% 1.28/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.28/0.57    inference(ennf_transformation,[],[f19])).
% 1.28/0.57  fof(f19,axiom,(
% 1.28/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.28/0.57  fof(f393,plain,(
% 1.28/0.57    ( ! [X3] : (r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0) | v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X3)) ) | ~spl8_31),
% 1.28/0.57    inference(avatar_component_clause,[],[f392])).
% 1.28/0.57  fof(f546,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(o_0_0_xboole_0,X0,X1) | ~r2_hidden(X2,X0) | o_0_0_xboole_0 = X1) ) | ~spl8_47),
% 1.28/0.57    inference(avatar_component_clause,[],[f545])).
% 1.28/0.57  fof(f1082,plain,(
% 1.28/0.57    ~spl8_9 | spl8_57),
% 1.28/0.57    inference(avatar_contradiction_clause,[],[f1081])).
% 1.28/0.57  fof(f1081,plain,(
% 1.28/0.57    $false | (~spl8_9 | spl8_57)),
% 1.28/0.57    inference(resolution,[],[f605,f202])).
% 1.28/0.57  fof(f605,plain,(
% 1.28/0.57    ~r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) | spl8_57),
% 1.28/0.57    inference(avatar_component_clause,[],[f603])).
% 1.28/0.57  fof(f603,plain,(
% 1.28/0.57    spl8_57 <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 1.28/0.57  fof(f1066,plain,(
% 1.28/0.57    ~spl8_57 | ~spl8_48),
% 1.28/0.57    inference(avatar_split_clause,[],[f1063,f548,f603])).
% 1.28/0.57  fof(f548,plain,(
% 1.28/0.57    spl8_48 <=> r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.28/0.57  fof(f1063,plain,(
% 1.28/0.57    ~r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) | ~spl8_48),
% 1.28/0.57    inference(resolution,[],[f550,f92])).
% 1.28/0.57  fof(f550,plain,(
% 1.28/0.57    r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0) | ~spl8_48),
% 1.28/0.57    inference(avatar_component_clause,[],[f548])).
% 1.28/0.57  fof(f1039,plain,(
% 1.28/0.57    spl8_47 | ~spl8_16 | spl8_48 | ~spl8_9 | ~spl8_11 | ~spl8_26),
% 1.28/0.57    inference(avatar_split_clause,[],[f1038,f343,f210,f194,f548,f249,f545])).
% 1.28/0.57  fof(f249,plain,(
% 1.28/0.57    spl8_16 <=> v1_funct_1(o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.28/0.57  fof(f210,plain,(
% 1.28/0.57    spl8_11 <=> o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.28/0.57  fof(f343,plain,(
% 1.28/0.57    spl8_26 <=> ! [X3] : (r2_hidden(X3,o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.28/0.57  fof(f1038,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (r2_hidden(o_0_0_xboole_0,o_0_0_xboole_0) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_funct_2(o_0_0_xboole_0,X0,X1) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0)) ) | (~spl8_9 | ~spl8_11 | ~spl8_26)),
% 1.28/0.57    inference(forward_demodulation,[],[f1037,f355])).
% 1.28/0.57  fof(f355,plain,(
% 1.28/0.57    ( ! [X0] : (o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X0)) ) | (~spl8_9 | ~spl8_26)),
% 1.28/0.57    inference(resolution,[],[f349,f202])).
% 1.28/0.57  fof(f349,plain,(
% 1.28/0.57    ( ! [X5] : (~r1_tarski(o_0_0_xboole_0,X5) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X5)) ) | ~spl8_26),
% 1.28/0.57    inference(resolution,[],[f344,f92])).
% 1.28/0.57  fof(f344,plain,(
% 1.28/0.57    ( ! [X3] : (r2_hidden(X3,o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3)) ) | ~spl8_26),
% 1.28/0.57    inference(avatar_component_clause,[],[f343])).
% 1.28/0.57  fof(f1037,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(o_0_0_xboole_0,X2),o_0_0_xboole_0) | ~v1_funct_1(o_0_0_xboole_0) | ~v1_funct_2(o_0_0_xboole_0,X0,X1) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0)) ) | (~spl8_9 | ~spl8_11)),
% 1.28/0.57    inference(forward_demodulation,[],[f998,f288])).
% 1.28/0.57  fof(f288,plain,(
% 1.28/0.57    ( ! [X0,X1] : (o_0_0_xboole_0 = k2_relset_1(X0,X1,o_0_0_xboole_0)) ) | (~spl8_9 | ~spl8_11)),
% 1.28/0.57    inference(forward_demodulation,[],[f284,f212])).
% 1.28/0.57  fof(f212,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) | ~spl8_11),
% 1.28/0.57    inference(avatar_component_clause,[],[f210])).
% 1.28/0.57  fof(f284,plain,(
% 1.28/0.57    ( ! [X0,X1] : (k2_relat_1(o_0_0_xboole_0) = k2_relset_1(X0,X1,o_0_0_xboole_0)) ) | ~spl8_9),
% 1.28/0.57    inference(resolution,[],[f96,f201])).
% 1.28/0.57  fof(f201,plain,(
% 1.28/0.57    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) ) | ~spl8_9),
% 1.28/0.57    inference(backward_demodulation,[],[f64,f196])).
% 1.28/0.57  fof(f64,plain,(
% 1.28/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.28/0.57    inference(cnf_transformation,[],[f11])).
% 1.28/0.57  fof(f11,axiom,(
% 1.28/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.28/0.57  fof(f998,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(o_0_0_xboole_0) | ~v1_funct_2(o_0_0_xboole_0,X0,X1) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(o_0_0_xboole_0,X2),k2_relset_1(X0,X1,o_0_0_xboole_0))) ) | ~spl8_9),
% 1.28/0.57    inference(resolution,[],[f531,f201])).
% 1.28/0.57  fof(f531,plain,(
% 1.28/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | o_0_0_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) ) | ~spl8_9),
% 1.28/0.57    inference(forward_demodulation,[],[f103,f196])).
% 1.28/0.57  fof(f103,plain,(
% 1.28/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 1.28/0.57    inference(cnf_transformation,[],[f52])).
% 1.28/0.57  fof(f52,plain,(
% 1.28/0.57    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.28/0.57    inference(flattening,[],[f51])).
% 1.28/0.57  fof(f51,plain,(
% 1.28/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.28/0.57    inference(ennf_transformation,[],[f26])).
% 1.28/0.57  fof(f26,axiom,(
% 1.28/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.28/0.57  fof(f1032,plain,(
% 1.28/0.57    spl8_52 | ~spl8_14 | ~spl8_5),
% 1.28/0.57    inference(avatar_split_clause,[],[f1029,f173,f237,f569])).
% 1.28/0.57  fof(f1029,plain,(
% 1.28/0.57    ( ! [X1] : (~v1_relat_1(sK2) | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(sK2) | k2_relat_1(sK2) = k2_enumset1(k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1),k1_funct_1(sK2,X1))) ) | ~spl8_5),
% 1.28/0.57    inference(resolution,[],[f120,f175])).
% 1.28/0.57  fof(f175,plain,(
% 1.28/0.57    v1_funct_1(sK2) | ~spl8_5),
% 1.28/0.57    inference(avatar_component_clause,[],[f173])).
% 1.28/0.57  fof(f120,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_enumset1(X0,X0,X0,X0) | k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) )),
% 1.28/0.57    inference(definition_unfolding,[],[f86,f114,f114])).
% 1.28/0.57  fof(f86,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))) )),
% 1.28/0.57    inference(cnf_transformation,[],[f41])).
% 1.28/0.57  fof(f41,plain,(
% 1.28/0.57    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.28/0.57    inference(flattening,[],[f40])).
% 1.28/0.57  fof(f40,plain,(
% 1.28/0.57    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.28/0.57    inference(ennf_transformation,[],[f18])).
% 1.28/0.57  fof(f18,axiom,(
% 1.28/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.28/0.57  fof(f1003,plain,(
% 1.28/0.57    spl8_12 | ~spl8_4 | ~spl8_5 | spl8_49 | ~spl8_3 | ~spl8_9 | ~spl8_19),
% 1.28/0.57    inference(avatar_split_clause,[],[f1002,f290,f194,f163,f554,f173,f168,f215])).
% 1.28/0.57  fof(f215,plain,(
% 1.28/0.57    spl8_12 <=> o_0_0_xboole_0 = sK1),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.28/0.57  fof(f168,plain,(
% 1.28/0.57    spl8_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.28/0.57  fof(f1002,plain,(
% 1.28/0.57    ( ! [X3] : (r2_hidden(k1_funct_1(sK2,X3),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | o_0_0_xboole_0 = sK1 | ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0))) ) | (~spl8_3 | ~spl8_9 | ~spl8_19)),
% 1.28/0.57    inference(forward_demodulation,[],[f999,f292])).
% 1.28/0.57  fof(f292,plain,(
% 1.28/0.57    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) | ~spl8_19),
% 1.28/0.57    inference(avatar_component_clause,[],[f290])).
% 1.28/0.57  fof(f999,plain,(
% 1.28/0.57    ( ! [X3] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | o_0_0_xboole_0 = sK1 | ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(k1_funct_1(sK2,X3),k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2))) ) | (~spl8_3 | ~spl8_9)),
% 1.28/0.57    inference(resolution,[],[f531,f165])).
% 1.28/0.57  fof(f955,plain,(
% 1.28/0.57    spl8_40 | ~spl8_14 | ~spl8_5),
% 1.28/0.57    inference(avatar_split_clause,[],[f952,f173,f237,f475])).
% 1.28/0.57  fof(f952,plain,(
% 1.28/0.57    ( ! [X2,X3] : (~v1_relat_1(sK2) | r2_hidden(sK5(sK2,X2,X3),X2) | r2_hidden(sK3(sK2,X2,X3),X3) | k9_relat_1(sK2,X2) = X3) ) | ~spl8_5),
% 1.28/0.57    inference(resolution,[],[f74,f175])).
% 1.28/0.57  fof(f74,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2) )),
% 1.28/0.57    inference(cnf_transformation,[],[f37])).
% 1.28/0.57  fof(f37,plain,(
% 1.28/0.57    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.57    inference(flattening,[],[f36])).
% 1.28/0.57  fof(f36,plain,(
% 1.28/0.57    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.57    inference(ennf_transformation,[],[f16])).
% 1.28/0.57  fof(f16,axiom,(
% 1.28/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 1.28/0.57  fof(f718,plain,(
% 1.28/0.57    ~spl8_6 | ~spl8_50),
% 1.28/0.57    inference(avatar_split_clause,[],[f627,f559,f178])).
% 1.28/0.57  fof(f178,plain,(
% 1.28/0.57    spl8_6 <=> v1_xboole_0(o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.28/0.57  fof(f627,plain,(
% 1.28/0.57    ~v1_xboole_0(o_0_0_xboole_0) | ~spl8_50),
% 1.28/0.57    inference(backward_demodulation,[],[f118,f560])).
% 1.28/0.57  fof(f560,plain,(
% 1.28/0.57    ( ! [X1] : (o_0_0_xboole_0 = X1) ) | ~spl8_50),
% 1.28/0.57    inference(avatar_component_clause,[],[f559])).
% 1.28/0.57  fof(f118,plain,(
% 1.28/0.57    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 1.28/0.57    inference(definition_unfolding,[],[f62,f114])).
% 1.28/0.57  fof(f62,plain,(
% 1.28/0.57    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.28/0.57    inference(cnf_transformation,[],[f7])).
% 1.28/0.57  fof(f7,axiom,(
% 1.28/0.57    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.28/0.57  fof(f490,plain,(
% 1.28/0.57    ~spl8_42 | spl8_1 | ~spl8_19),
% 1.28/0.57    inference(avatar_split_clause,[],[f485,f290,f153,f487])).
% 1.28/0.57  fof(f153,plain,(
% 1.28/0.57    spl8_1 <=> k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.28/0.57  fof(f485,plain,(
% 1.28/0.57    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | (spl8_1 | ~spl8_19)),
% 1.28/0.57    inference(forward_demodulation,[],[f155,f292])).
% 1.28/0.57  fof(f155,plain,(
% 1.28/0.57    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) | spl8_1),
% 1.28/0.57    inference(avatar_component_clause,[],[f153])).
% 1.28/0.57  fof(f394,plain,(
% 1.28/0.57    ~spl8_13 | spl8_31 | ~spl8_10 | ~spl8_16),
% 1.28/0.57    inference(avatar_split_clause,[],[f390,f249,f205,f392,f229])).
% 1.28/0.57  fof(f229,plain,(
% 1.28/0.57    spl8_13 <=> v1_relat_1(o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.28/0.57  fof(f205,plain,(
% 1.28/0.57    spl8_10 <=> o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.28/0.57  fof(f390,plain,(
% 1.28/0.57    ( ! [X3] : (v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,X3) | r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0)) ) | (~spl8_10 | ~spl8_16)),
% 1.28/0.57    inference(forward_demodulation,[],[f389,f207])).
% 1.28/0.57  fof(f207,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) | ~spl8_10),
% 1.28/0.57    inference(avatar_component_clause,[],[f205])).
% 1.28/0.57  fof(f389,plain,(
% 1.28/0.57    ( ! [X3] : (r2_hidden(sK7(o_0_0_xboole_0,X3,o_0_0_xboole_0),o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | v1_funct_2(o_0_0_xboole_0,k1_relat_1(o_0_0_xboole_0),X3)) ) | (~spl8_10 | ~spl8_16)),
% 1.28/0.57    inference(forward_demodulation,[],[f381,f207])).
% 1.28/0.57  fof(f381,plain,(
% 1.28/0.57    ( ! [X3] : (~v1_relat_1(o_0_0_xboole_0) | r2_hidden(sK7(k1_relat_1(o_0_0_xboole_0),X3,o_0_0_xboole_0),k1_relat_1(o_0_0_xboole_0)) | v1_funct_2(o_0_0_xboole_0,k1_relat_1(o_0_0_xboole_0),X3)) ) | ~spl8_16),
% 1.28/0.57    inference(resolution,[],[f141,f251])).
% 1.28/0.57  fof(f251,plain,(
% 1.28/0.57    v1_funct_1(o_0_0_xboole_0) | ~spl8_16),
% 1.28/0.57    inference(avatar_component_clause,[],[f249])).
% 1.28/0.57  fof(f141,plain,(
% 1.28/0.57    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | v1_funct_2(X2,k1_relat_1(X2),X1)) )),
% 1.28/0.57    inference(equality_resolution,[],[f100])).
% 1.28/0.57  fof(f100,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK7(X0,X1,X2),X0) | v1_funct_2(X2,X0,X1)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f48])).
% 1.28/0.57  fof(f345,plain,(
% 1.28/0.57    ~spl8_13 | spl8_26 | ~spl8_9 | ~spl8_10 | ~spl8_16),
% 1.28/0.57    inference(avatar_split_clause,[],[f341,f249,f205,f194,f343,f229])).
% 1.28/0.57  fof(f341,plain,(
% 1.28/0.57    ( ! [X3] : (r2_hidden(X3,o_0_0_xboole_0) | ~v1_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3)) ) | (~spl8_9 | ~spl8_10 | ~spl8_16)),
% 1.28/0.57    inference(forward_demodulation,[],[f335,f207])).
% 1.28/0.57  fof(f335,plain,(
% 1.28/0.57    ( ! [X3] : (~v1_relat_1(o_0_0_xboole_0) | o_0_0_xboole_0 = k1_funct_1(o_0_0_xboole_0,X3) | r2_hidden(X3,k1_relat_1(o_0_0_xboole_0))) ) | (~spl8_9 | ~spl8_16)),
% 1.28/0.57    inference(resolution,[],[f327,f251])).
% 1.28/0.57  fof(f327,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | o_0_0_xboole_0 = k1_funct_1(X0,X1) | r2_hidden(X1,k1_relat_1(X0))) ) | ~spl8_9),
% 1.28/0.57    inference(forward_demodulation,[],[f131,f196])).
% 1.28/0.57  fof(f131,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = k1_funct_1(X0,X1)) )),
% 1.28/0.57    inference(equality_resolution,[],[f69])).
% 1.28/0.57  fof(f69,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(X1,k1_relat_1(X0)) | k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2) )),
% 1.28/0.57    inference(cnf_transformation,[],[f35])).
% 1.28/0.57  fof(f35,plain,(
% 1.28/0.57    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.57    inference(flattening,[],[f34])).
% 1.28/0.57  fof(f34,plain,(
% 1.28/0.57    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.57    inference(ennf_transformation,[],[f17])).
% 1.28/0.57  % (5256)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.57  fof(f17,axiom,(
% 1.28/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 1.28/0.57  fof(f339,plain,(
% 1.28/0.57    spl8_25 | ~spl8_14 | ~spl8_5 | ~spl8_9),
% 1.28/0.57    inference(avatar_split_clause,[],[f333,f194,f173,f237,f337])).
% 1.28/0.57  fof(f333,plain,(
% 1.28/0.57    ( ! [X0] : (~v1_relat_1(sK2) | o_0_0_xboole_0 = k1_funct_1(sK2,X0) | r2_hidden(X0,k1_relat_1(sK2))) ) | (~spl8_5 | ~spl8_9)),
% 1.28/0.57    inference(resolution,[],[f327,f175])).
% 1.28/0.57  fof(f304,plain,(
% 1.28/0.57    spl8_20 | ~spl8_3 | ~spl8_18),
% 1.28/0.57    inference(avatar_split_clause,[],[f299,f280,f163,f301])).
% 1.28/0.57  fof(f299,plain,(
% 1.28/0.57    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) | (~spl8_3 | ~spl8_18)),
% 1.28/0.57    inference(forward_demodulation,[],[f295,f282])).
% 1.28/0.57  fof(f282,plain,(
% 1.28/0.57    k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k1_relat_1(sK2) | ~spl8_18),
% 1.28/0.57    inference(avatar_component_clause,[],[f280])).
% 1.28/0.57  fof(f295,plain,(
% 1.28/0.57    m1_subset_1(k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl8_3),
% 1.28/0.57    inference(resolution,[],[f97,f165])).
% 1.28/0.57  fof(f97,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.28/0.57    inference(cnf_transformation,[],[f46])).
% 1.28/0.57  fof(f46,plain,(
% 1.28/0.57    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.57    inference(ennf_transformation,[],[f21])).
% 1.28/0.57  fof(f21,axiom,(
% 1.28/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.28/0.57  fof(f258,plain,(
% 1.28/0.57    ~spl8_14 | ~spl8_5 | ~spl8_17),
% 1.28/0.57    inference(avatar_split_clause,[],[f256,f253,f173,f237])).
% 1.28/0.57  fof(f253,plain,(
% 1.28/0.57    spl8_17 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.28/0.57  fof(f256,plain,(
% 1.28/0.57    ~v1_relat_1(sK2) | (~spl8_5 | ~spl8_17)),
% 1.28/0.57    inference(resolution,[],[f254,f175])).
% 1.28/0.57  fof(f254,plain,(
% 1.28/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_17),
% 1.28/0.57    inference(avatar_component_clause,[],[f253])).
% 1.28/0.57  fof(f255,plain,(
% 1.28/0.57    spl8_16 | spl8_17 | ~spl8_9),
% 1.28/0.57    inference(avatar_split_clause,[],[f246,f194,f253,f249])).
% 1.28/0.57  fof(f246,plain,(
% 1.28/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(o_0_0_xboole_0)) ) | ~spl8_9),
% 1.28/0.57    inference(resolution,[],[f67,f201])).
% 1.28/0.57  fof(f67,plain,(
% 1.28/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(X1)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f33])).
% 1.28/0.57  fof(f33,plain,(
% 1.28/0.57    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.28/0.57    inference(flattening,[],[f32])).
% 1.28/0.57  fof(f32,plain,(
% 1.28/0.57    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.28/0.57    inference(ennf_transformation,[],[f15])).
% 1.28/0.57  fof(f15,axiom,(
% 1.28/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).
% 1.28/0.57  fof(f240,plain,(
% 1.28/0.57    spl8_14 | ~spl8_3),
% 1.28/0.57    inference(avatar_split_clause,[],[f234,f163,f237])).
% 1.28/0.57  fof(f234,plain,(
% 1.28/0.57    v1_relat_1(sK2) | ~spl8_3),
% 1.28/0.57    inference(resolution,[],[f165,f94])).
% 1.28/0.57  fof(f94,plain,(
% 1.28/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.28/0.57    inference(cnf_transformation,[],[f43])).
% 1.28/0.57  fof(f43,plain,(
% 1.28/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.57    inference(ennf_transformation,[],[f20])).
% 1.28/0.57  fof(f20,axiom,(
% 1.28/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.28/0.57  fof(f232,plain,(
% 1.28/0.57    spl8_13 | ~spl8_9),
% 1.28/0.57    inference(avatar_split_clause,[],[f225,f194,f229])).
% 1.28/0.57  fof(f225,plain,(
% 1.28/0.57    v1_relat_1(o_0_0_xboole_0) | ~spl8_9),
% 1.28/0.57    inference(resolution,[],[f94,f201])).
% 1.28/0.57  fof(f218,plain,(
% 1.28/0.57    ~spl8_12 | spl8_2 | ~spl8_9),
% 1.28/0.57    inference(avatar_split_clause,[],[f203,f194,f158,f215])).
% 1.28/0.57  fof(f158,plain,(
% 1.28/0.57    spl8_2 <=> k1_xboole_0 = sK1),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.28/0.57  fof(f203,plain,(
% 1.28/0.57    o_0_0_xboole_0 != sK1 | (spl8_2 | ~spl8_9)),
% 1.28/0.57    inference(backward_demodulation,[],[f160,f196])).
% 1.28/0.57  fof(f160,plain,(
% 1.28/0.57    k1_xboole_0 != sK1 | spl8_2),
% 1.28/0.57    inference(avatar_component_clause,[],[f158])).
% 1.28/0.57  fof(f213,plain,(
% 1.28/0.57    spl8_11 | ~spl8_7 | ~spl8_9),
% 1.28/0.57    inference(avatar_split_clause,[],[f200,f194,f183,f210])).
% 1.28/0.57  fof(f183,plain,(
% 1.28/0.57    spl8_7 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.28/0.57  fof(f200,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) | (~spl8_7 | ~spl8_9)),
% 1.28/0.57    inference(backward_demodulation,[],[f185,f196])).
% 1.28/0.57  fof(f185,plain,(
% 1.28/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_7),
% 1.28/0.57    inference(avatar_component_clause,[],[f183])).
% 1.28/0.57  fof(f208,plain,(
% 1.28/0.57    spl8_10 | ~spl8_8 | ~spl8_9),
% 1.28/0.57    inference(avatar_split_clause,[],[f199,f194,f188,f205])).
% 1.28/0.57  fof(f188,plain,(
% 1.28/0.57    spl8_8 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.28/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.28/0.57  fof(f199,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) | (~spl8_8 | ~spl8_9)),
% 1.28/0.57    inference(backward_demodulation,[],[f190,f196])).
% 1.28/0.57  fof(f190,plain,(
% 1.28/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_8),
% 1.28/0.57    inference(avatar_component_clause,[],[f188])).
% 1.28/0.57  fof(f197,plain,(
% 1.28/0.57    spl8_9 | ~spl8_6),
% 1.28/0.57    inference(avatar_split_clause,[],[f192,f178,f194])).
% 1.28/0.57  fof(f192,plain,(
% 1.28/0.57    o_0_0_xboole_0 = k1_xboole_0 | ~spl8_6),
% 1.28/0.57    inference(resolution,[],[f66,f180])).
% 1.28/0.57  fof(f180,plain,(
% 1.28/0.57    v1_xboole_0(o_0_0_xboole_0) | ~spl8_6),
% 1.28/0.57    inference(avatar_component_clause,[],[f178])).
% 1.28/0.57  fof(f66,plain,(
% 1.28/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.28/0.57    inference(cnf_transformation,[],[f31])).
% 1.28/0.57  fof(f31,plain,(
% 1.28/0.57    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.28/0.57    inference(ennf_transformation,[],[f2])).
% 1.28/0.57  fof(f2,axiom,(
% 1.28/0.57    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.28/0.57  fof(f191,plain,(
% 1.28/0.57    spl8_8),
% 1.28/0.57    inference(avatar_split_clause,[],[f60,f188])).
% 1.28/0.57  fof(f60,plain,(
% 1.28/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.28/0.57    inference(cnf_transformation,[],[f14])).
% 1.28/0.57  fof(f14,axiom,(
% 1.28/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.28/0.57  fof(f186,plain,(
% 1.28/0.57    spl8_7),
% 1.28/0.57    inference(avatar_split_clause,[],[f61,f183])).
% 1.28/0.57  fof(f61,plain,(
% 1.28/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.28/0.57    inference(cnf_transformation,[],[f14])).
% 1.28/0.57  fof(f181,plain,(
% 1.28/0.57    spl8_6),
% 1.28/0.57    inference(avatar_split_clause,[],[f59,f178])).
% 1.28/0.57  fof(f59,plain,(
% 1.28/0.57    v1_xboole_0(o_0_0_xboole_0)),
% 1.28/0.57    inference(cnf_transformation,[],[f1])).
% 1.28/0.57  fof(f1,axiom,(
% 1.28/0.57    v1_xboole_0(o_0_0_xboole_0)),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 1.28/0.57  fof(f176,plain,(
% 1.28/0.57    spl8_5),
% 1.28/0.57    inference(avatar_split_clause,[],[f54,f173])).
% 1.28/0.57  fof(f54,plain,(
% 1.28/0.57    v1_funct_1(sK2)),
% 1.28/0.57    inference(cnf_transformation,[],[f30])).
% 1.28/0.57  fof(f30,plain,(
% 1.28/0.57    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.28/0.57    inference(flattening,[],[f29])).
% 1.28/0.57  fof(f29,plain,(
% 1.28/0.57    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.28/0.57    inference(ennf_transformation,[],[f28])).
% 1.28/0.57  fof(f28,negated_conjecture,(
% 1.28/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.28/0.57    inference(negated_conjecture,[],[f27])).
% 1.28/0.57  fof(f27,conjecture,(
% 1.28/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 1.28/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).
% 1.28/0.57  fof(f171,plain,(
% 1.28/0.57    spl8_4),
% 1.28/0.57    inference(avatar_split_clause,[],[f117,f168])).
% 1.28/0.57  fof(f117,plain,(
% 1.28/0.57    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 1.28/0.57    inference(definition_unfolding,[],[f55,f114])).
% 1.28/0.57  fof(f55,plain,(
% 1.28/0.57    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 1.28/0.57    inference(cnf_transformation,[],[f30])).
% 1.28/0.57  fof(f166,plain,(
% 1.28/0.57    spl8_3),
% 1.28/0.57    inference(avatar_split_clause,[],[f116,f163])).
% 1.28/0.57  fof(f116,plain,(
% 1.28/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 1.28/0.57    inference(definition_unfolding,[],[f56,f114])).
% 1.28/0.57  fof(f56,plain,(
% 1.28/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 1.28/0.57    inference(cnf_transformation,[],[f30])).
% 1.28/0.57  fof(f161,plain,(
% 1.28/0.57    ~spl8_2),
% 1.28/0.57    inference(avatar_split_clause,[],[f57,f158])).
% 1.28/0.57  fof(f57,plain,(
% 1.28/0.57    k1_xboole_0 != sK1),
% 1.28/0.57    inference(cnf_transformation,[],[f30])).
% 1.28/0.57  fof(f156,plain,(
% 1.28/0.57    ~spl8_1),
% 1.28/0.57    inference(avatar_split_clause,[],[f115,f153])).
% 1.28/0.57  fof(f115,plain,(
% 1.28/0.57    k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0))),
% 1.28/0.57    inference(definition_unfolding,[],[f58,f114,f114])).
% 1.28/0.57  fof(f58,plain,(
% 1.28/0.57    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 1.28/0.57    inference(cnf_transformation,[],[f30])).
% 1.28/0.57  % SZS output end Proof for theBenchmark
% 1.28/0.57  % (5248)------------------------------
% 1.28/0.57  % (5248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.57  % (5248)Termination reason: Refutation
% 1.28/0.57  
% 1.28/0.57  % (5248)Memory used [KB]: 12281
% 1.28/0.57  % (5248)Time elapsed: 0.152 s
% 1.28/0.57  % (5248)------------------------------
% 1.28/0.57  % (5248)------------------------------
% 1.28/0.57  % (5252)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.57  % (5231)Success in time 0.208 s
%------------------------------------------------------------------------------
