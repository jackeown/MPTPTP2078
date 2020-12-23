%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0354+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 3.71s
% Output     : Refutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 193 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :    8
%              Number of atoms          :  238 ( 426 expanded)
%              Number of equality atoms :   65 ( 121 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6086,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1256,f1261,f1266,f1363,f1447,f1448,f1494,f1505,f1649,f1654,f1766,f1838,f1844,f3129,f3436,f4528,f6055])).

fof(f6055,plain,
    ( ~ spl30_2
    | ~ spl30_79
    | spl30_342 ),
    inference(avatar_contradiction_clause,[],[f6054])).

fof(f6054,plain,
    ( $false
    | ~ spl30_2
    | ~ spl30_79
    | spl30_342 ),
    inference(subsumption_resolution,[],[f6053,f4527])).

fof(f4527,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | spl30_342 ),
    inference(avatar_component_clause,[],[f4525])).

fof(f4525,plain,
    ( spl30_342
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_342])])).

fof(f6053,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl30_2
    | ~ spl30_79 ),
    inference(forward_demodulation,[],[f5656,f861])).

fof(f861,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5656,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl30_2
    | ~ spl30_79 ),
    inference(unit_resulting_resolution,[],[f1260,f1837,f815])).

fof(f815,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f508])).

fof(f508,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f507])).

fof(f507,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f479])).

fof(f479,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1837,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl30_79 ),
    inference(avatar_component_clause,[],[f1835])).

fof(f1835,plain,
    ( spl30_79
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_79])])).

fof(f1260,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl30_2 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f1258,plain,
    ( spl30_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_2])])).

fof(f4528,plain,
    ( ~ spl30_342
    | ~ spl30_186
    | spl30_230 ),
    inference(avatar_split_clause,[],[f4498,f3433,f2949,f4525])).

fof(f2949,plain,
    ( spl30_186
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_186])])).

fof(f3433,plain,
    ( spl30_230
  <=> k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_230])])).

fof(f4498,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl30_186
    | spl30_230 ),
    inference(backward_demodulation,[],[f3435,f4471])).

fof(f4471,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(X2,sK2)) = k2_xboole_0(sK2,k4_xboole_0(sK0,X2))
    | ~ spl30_186 ),
    inference(forward_demodulation,[],[f4428,f861])).

fof(f4428,plain,
    ( ! [X2] : k4_xboole_0(sK0,k4_xboole_0(X2,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X2),sK2)
    | ~ spl30_186 ),
    inference(superposition,[],[f935,f2951])).

fof(f2951,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl30_186 ),
    inference(avatar_component_clause,[],[f2949])).

fof(f935,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f3435,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl30_230 ),
    inference(avatar_component_clause,[],[f3433])).

fof(f3436,plain,
    ( ~ spl30_230
    | ~ spl30_3
    | spl30_80 ),
    inference(avatar_split_clause,[],[f3385,f1841,f1263,f3433])).

fof(f1263,plain,
    ( spl30_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_3])])).

fof(f1841,plain,
    ( spl30_80
  <=> k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) = k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_80])])).

fof(f3385,plain,
    ( k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl30_3
    | spl30_80 ),
    inference(backward_demodulation,[],[f1843,f3309])).

fof(f3309,plain,
    ( ! [X0] : k3_subset_1(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0))
    | ~ spl30_3 ),
    inference(unit_resulting_resolution,[],[f1644,f825])).

fof(f825,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f517])).

fof(f517,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1644,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
    | ~ spl30_3 ),
    inference(backward_demodulation,[],[f1577,f1576])).

fof(f1576,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)
    | ~ spl30_3 ),
    inference(unit_resulting_resolution,[],[f1265,f827])).

fof(f827,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f519])).

fof(f519,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f482])).

fof(f482,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1265,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl30_3 ),
    inference(avatar_component_clause,[],[f1263])).

fof(f1577,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(sK0,sK1,X0),k1_zfmisc_1(sK0))
    | ~ spl30_3 ),
    inference(unit_resulting_resolution,[],[f1265,f828])).

fof(f828,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f520])).

fof(f520,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f465])).

fof(f465,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f1843,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)
    | spl30_80 ),
    inference(avatar_component_clause,[],[f1841])).

fof(f3129,plain,
    ( spl30_186
    | ~ spl30_27
    | ~ spl30_34 ),
    inference(avatar_split_clause,[],[f3128,f1502,f1455,f2949])).

fof(f1455,plain,
    ( spl30_27
  <=> sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_27])])).

fof(f1502,plain,
    ( spl30_34
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_34])])).

fof(f3128,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl30_27
    | ~ spl30_34 ),
    inference(forward_demodulation,[],[f3127,f1457])).

fof(f1457,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl30_27 ),
    inference(avatar_component_clause,[],[f1455])).

fof(f3127,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(sK0,sK2)
    | ~ spl30_34 ),
    inference(forward_demodulation,[],[f2849,f950])).

fof(f950,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2849,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl30_34 ),
    inference(resolution,[],[f1504,f825])).

fof(f1504,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl30_34 ),
    inference(avatar_component_clause,[],[f1502])).

fof(f1844,plain,
    ( ~ spl30_80
    | spl30_48
    | ~ spl30_50 ),
    inference(avatar_split_clause,[],[f1839,f1656,f1646,f1841])).

fof(f1646,plain,
    ( spl30_48
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) = k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_48])])).

fof(f1656,plain,
    ( spl30_50
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_50])])).

fof(f1839,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK1,sK2)) != k4_subset_1(sK0,k4_xboole_0(sK0,sK1),sK2)
    | spl30_48
    | ~ spl30_50 ),
    inference(forward_demodulation,[],[f1648,f1658])).

fof(f1658,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl30_50 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f1648,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2))
    | spl30_48 ),
    inference(avatar_component_clause,[],[f1646])).

fof(f1838,plain,
    ( spl30_79
    | ~ spl30_49
    | ~ spl30_50 ),
    inference(avatar_split_clause,[],[f1833,f1656,f1651,f1835])).

fof(f1651,plain,
    ( spl30_49
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_49])])).

fof(f1833,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl30_49
    | ~ spl30_50 ),
    inference(forward_demodulation,[],[f1653,f1658])).

fof(f1653,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl30_49 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f1766,plain,
    ( spl30_50
    | ~ spl30_3 ),
    inference(avatar_split_clause,[],[f1596,f1263,f1656])).

fof(f1596,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl30_3 ),
    inference(resolution,[],[f1265,f825])).

fof(f1654,plain,
    ( spl30_49
    | ~ spl30_3 ),
    inference(avatar_split_clause,[],[f1575,f1263,f1651])).

fof(f1575,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl30_3 ),
    inference(unit_resulting_resolution,[],[f1265,f826])).

fof(f826,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f518])).

fof(f518,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f461])).

fof(f461,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1649,plain,
    ( ~ spl30_48
    | spl30_1
    | ~ spl30_3 ),
    inference(avatar_split_clause,[],[f1643,f1263,f1253,f1646])).

fof(f1253,plain,
    ( spl30_1
  <=> k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) = k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_1])])).

fof(f1643,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) != k3_subset_1(sK0,k4_xboole_0(sK1,sK2))
    | spl30_1
    | ~ spl30_3 ),
    inference(backward_demodulation,[],[f1255,f1576])).

fof(f1255,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
    | spl30_1 ),
    inference(avatar_component_clause,[],[f1253])).

fof(f1505,plain,
    ( spl30_34
    | ~ spl30_11
    | ~ spl30_12 ),
    inference(avatar_split_clause,[],[f1500,f1365,f1360,f1502])).

fof(f1360,plain,
    ( spl30_11
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_11])])).

fof(f1365,plain,
    ( spl30_12
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_12])])).

fof(f1500,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl30_11
    | ~ spl30_12 ),
    inference(forward_demodulation,[],[f1362,f1367])).

fof(f1367,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl30_12 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1362,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl30_11 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f1494,plain,
    ( spl30_27
    | ~ spl30_12
    | ~ spl30_13 ),
    inference(avatar_split_clause,[],[f1491,f1370,f1365,f1455])).

fof(f1370,plain,
    ( spl30_13
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl30_13])])).

fof(f1491,plain,
    ( sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl30_12
    | ~ spl30_13 ),
    inference(backward_demodulation,[],[f1372,f1367])).

fof(f1372,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl30_13 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f1448,plain,
    ( spl30_12
    | ~ spl30_2 ),
    inference(avatar_split_clause,[],[f1313,f1258,f1365])).

fof(f1313,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl30_2 ),
    inference(resolution,[],[f1260,f825])).

fof(f1447,plain,
    ( spl30_13
    | ~ spl30_2 ),
    inference(avatar_split_clause,[],[f1312,f1258,f1370])).

fof(f1312,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl30_2 ),
    inference(resolution,[],[f1260,f824])).

fof(f824,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f516])).

fof(f516,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f475])).

fof(f475,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1363,plain,
    ( spl30_11
    | ~ spl30_2 ),
    inference(avatar_split_clause,[],[f1294,f1258,f1360])).

fof(f1294,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl30_2 ),
    inference(unit_resulting_resolution,[],[f1260,f826])).

fof(f1266,plain,(
    spl30_3 ),
    inference(avatar_split_clause,[],[f811,f1263])).

fof(f811,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f698])).

fof(f698,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f504,f697,f696])).

fof(f696,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f697,plain,
    ( ? [X2] :
        ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,X2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f504,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) != k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f495])).

fof(f495,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f1261,plain,(
    spl30_2 ),
    inference(avatar_split_clause,[],[f812,f1258])).

fof(f812,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f698])).

fof(f1256,plain,(
    ~ spl30_1 ),
    inference(avatar_split_clause,[],[f813,f1253])).

fof(f813,plain,(
    k3_subset_1(sK0,k7_subset_1(sK0,sK1,sK2)) != k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f698])).
%------------------------------------------------------------------------------
