%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 390 expanded)
%              Number of leaves         :   48 ( 167 expanded)
%              Depth                    :   10
%              Number of atoms          :  380 ( 759 expanded)
%              Number of equality atoms :  140 ( 346 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25975)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f2083,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f79,f100,f111,f115,f137,f175,f411,f416,f803,f1011,f1294,f1298,f1316,f1355,f1398,f1451,f1646,f1663,f1829,f1834,f1851,f1896,f2032,f2074,f2078,f2082])).

% (25969)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f2082,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK1)
    | sK1 != k4_xboole_0(sK1,sK3)
    | sK2 != k2_xboole_0(k4_xboole_0(sK2,sK1),sK1)
    | sK1 != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2078,plain,
    ( spl6_116
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f2064,f2030,f2076])).

fof(f2076,plain,
    ( spl6_116
  <=> sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f2030,plain,
    ( spl6_112
  <=> sK1 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f2064,plain,
    ( sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1)
    | ~ spl6_112 ),
    inference(superposition,[],[f55,f2031])).

fof(f2031,plain,
    ( sK1 = k4_xboole_0(sK2,sK0)
    | ~ spl6_112 ),
    inference(avatar_component_clause,[],[f2030])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f2074,plain,
    ( spl6_115
    | ~ spl6_28
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f2073,f2030,f414,f2070])).

fof(f2070,plain,
    ( spl6_115
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f414,plain,
    ( spl6_28
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f2073,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl6_28
    | ~ spl6_112 ),
    inference(forward_demodulation,[],[f2063,f415])).

fof(f415,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f414])).

fof(f2063,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK1)
    | ~ spl6_112 ),
    inference(superposition,[],[f54,f2031])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f43,f43])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2032,plain,
    ( spl6_112
    | ~ spl6_38
    | ~ spl6_98
    | ~ spl6_101 ),
    inference(avatar_split_clause,[],[f2028,f1874,f1827,f784,f2030])).

fof(f784,plain,
    ( spl6_38
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f1827,plain,
    ( spl6_98
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f1874,plain,
    ( spl6_101
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f2028,plain,
    ( sK1 = k4_xboole_0(sK2,sK0)
    | ~ spl6_38
    | ~ spl6_98
    | ~ spl6_101 ),
    inference(forward_demodulation,[],[f2027,f1875])).

fof(f1875,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl6_101 ),
    inference(avatar_component_clause,[],[f1874])).

fof(f2027,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_38
    | ~ spl6_98 ),
    inference(forward_demodulation,[],[f2026,f1828])).

fof(f1828,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f1827])).

fof(f2026,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k4_xboole_0(sK1,sK0)
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1992,f128])).

fof(f128,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1992,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl6_38 ),
    inference(superposition,[],[f128,f785])).

fof(f785,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f784])).

fof(f1896,plain,
    ( spl6_101
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f1865,f1849,f1874])).

fof(f1849,plain,
    ( spl6_100
  <=> sK2 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1865,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl6_100 ),
    inference(superposition,[],[f42,f1850])).

fof(f1850,plain,
    ( sK2 = k2_xboole_0(sK2,sK1)
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1849])).

fof(f1851,plain,
    ( spl6_100
    | ~ spl6_99 ),
    inference(avatar_split_clause,[],[f1847,f1832,f1849])).

fof(f1832,plain,
    ( spl6_99
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f1847,plain,
    ( sK2 = k2_xboole_0(sK2,sK1)
    | ~ spl6_99 ),
    inference(forward_demodulation,[],[f1841,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1841,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_99 ),
    inference(superposition,[],[f45,f1833])).

fof(f1833,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f1832])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1834,plain,
    ( spl6_99
    | ~ spl6_78
    | ~ spl6_83 ),
    inference(avatar_split_clause,[],[f1830,f1446,f1395,f1832])).

fof(f1395,plain,
    ( spl6_78
  <=> sK1 = k4_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1446,plain,
    ( spl6_83
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f1830,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl6_78
    | ~ spl6_83 ),
    inference(forward_demodulation,[],[f1805,f103])).

fof(f103,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(resolution,[],[f50,f83])).

fof(f83,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f40,f42])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1805,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2)
    | ~ spl6_78
    | ~ spl6_83 ),
    inference(superposition,[],[f1425,f1447])).

fof(f1447,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f1446])).

fof(f1425,plain,
    ( ! [X3] : k4_xboole_0(sK1,k2_xboole_0(sK3,X3)) = k4_xboole_0(sK1,X3)
    | ~ spl6_78 ),
    inference(superposition,[],[f51,f1396])).

fof(f1396,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1395])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1829,plain,
    ( spl6_98
    | ~ spl6_78
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f1825,f1661,f1395,f1827])).

fof(f1661,plain,
    ( spl6_94
  <=> sK3 = k2_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f1825,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl6_78
    | ~ spl6_94 ),
    inference(forward_demodulation,[],[f1804,f1396])).

fof(f1804,plain,
    ( k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0)
    | ~ spl6_78
    | ~ spl6_94 ),
    inference(superposition,[],[f1425,f1662])).

fof(f1662,plain,
    ( sK3 = k2_xboole_0(sK3,sK0)
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f1661])).

% (25955)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f1663,plain,
    ( spl6_94
    | ~ spl6_93 ),
    inference(avatar_split_clause,[],[f1659,f1644,f1661])).

fof(f1644,plain,
    ( spl6_93
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f1659,plain,
    ( sK3 = k2_xboole_0(sK3,sK0)
    | ~ spl6_93 ),
    inference(forward_demodulation,[],[f1654,f38])).

fof(f1654,plain,
    ( k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_93 ),
    inference(superposition,[],[f45,f1645])).

fof(f1645,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK3)
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f1644])).

fof(f1646,plain,
    ( spl6_93
    | ~ spl6_4
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f1642,f1352,f71,f1644])).

fof(f71,plain,
    ( spl6_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1352,plain,
    ( spl6_74
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1642,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK3)
    | ~ spl6_4
    | ~ spl6_74 ),
    inference(forward_demodulation,[],[f1627,f102])).

fof(f102,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f50,f40])).

fof(f1627,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3)
    | ~ spl6_4
    | ~ spl6_74 ),
    inference(superposition,[],[f1376,f72])).

fof(f72,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f1376,plain,
    ( ! [X3] : k4_xboole_0(sK0,k2_xboole_0(sK2,X3)) = k4_xboole_0(sK0,X3)
    | ~ spl6_74 ),
    inference(superposition,[],[f51,f1353])).

fof(f1353,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f1451,plain,
    ( spl6_83
    | ~ spl6_73 ),
    inference(avatar_split_clause,[],[f1435,f1314,f1446])).

fof(f1314,plain,
    ( spl6_73
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f1435,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)
    | ~ spl6_73 ),
    inference(superposition,[],[f45,f1315])).

fof(f1315,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f1314])).

fof(f1398,plain,
    ( spl6_78
    | ~ spl6_71 ),
    inference(avatar_split_clause,[],[f1383,f1296,f1395])).

% (25956)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f1296,plain,
    ( spl6_71
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f1383,plain,
    ( sK1 = k4_xboole_0(sK1,sK3)
    | ~ spl6_71 ),
    inference(superposition,[],[f80,f1297])).

fof(f1297,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f1296])).

fof(f80,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f42,f38])).

% (25976)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f1355,plain,
    ( spl6_74
    | ~ spl6_70 ),
    inference(avatar_split_clause,[],[f1340,f1292,f1352])).

fof(f1292,plain,
    ( spl6_70
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f1340,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl6_70 ),
    inference(superposition,[],[f80,f1293])).

fof(f1293,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f1316,plain,
    ( spl6_73
    | ~ spl6_9
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f1312,f977,f135,f1314])).

fof(f135,plain,
    ( spl6_9
  <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f977,plain,
    ( spl6_53
  <=> sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f1312,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))
    | ~ spl6_9
    | ~ spl6_53 ),
    inference(forward_demodulation,[],[f1252,f978])).

% (25961)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f978,plain,
    ( sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f977])).

fof(f1252,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3))
    | ~ spl6_9 ),
    inference(superposition,[],[f55,f136])).

fof(f136,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f1298,plain,
    ( spl6_71
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f1240,f409,f1296])).

fof(f409,plain,
    ( spl6_27
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1240,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))
    | ~ spl6_27 ),
    inference(superposition,[],[f55,f410])).

fof(f410,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f409])).

fof(f1294,plain,
    ( spl6_70
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f1239,f414,f1292])).

fof(f1239,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | ~ spl6_28 ),
    inference(superposition,[],[f55,f415])).

fof(f1011,plain,
    ( spl6_53
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f1010,f135,f113,f977])).

fof(f113,plain,
    ( spl6_8
  <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1010,plain,
    ( sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3))
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f1009,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1009,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f946,f114])).

fof(f114,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f946,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)))
    | ~ spl6_9 ),
    inference(superposition,[],[f54,f136])).

fof(f803,plain,
    ( spl6_38
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f750,f173,f784])).

fof(f173,plain,
    ( spl6_11
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f750,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl6_11 ),
    inference(superposition,[],[f174,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f174,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f416,plain,
    ( spl6_28
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f412,f67,f414])).

fof(f67,plain,
    ( spl6_3
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

% (25950)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f412,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl6_3 ),
    inference(resolution,[],[f406,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f406,plain,
    ( ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f404,f54])).

fof(f404,plain,
    ( ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))
    | ~ spl6_3 ),
    inference(resolution,[],[f56,f68])).

fof(f68,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f411,plain,
    ( spl6_27
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f407,f63,f409])).

fof(f63,plain,
    ( spl6_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f407,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl6_2 ),
    inference(resolution,[],[f405,f39])).

fof(f405,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f403,f54])).

fof(f403,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f64])).

fof(f64,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f175,plain,
    ( spl6_11
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f171,f109,f173])).

fof(f109,plain,
    ( spl6_7
  <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f171,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f149,f38])).

fof(f149,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl6_7 ),
    inference(superposition,[],[f45,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f137,plain,
    ( spl6_9
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f127,f71,f135])).

fof(f127,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl6_4 ),
    inference(superposition,[],[f44,f72])).

fof(f115,plain,
    ( spl6_8
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f105,f98,f113])).

fof(f98,plain,
    ( spl6_6
  <=> r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f105,plain,
    ( k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f50,f99])).

fof(f99,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f111,plain,
    ( spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f104,f77,f109])).

fof(f77,plain,
    ( spl6_5
  <=> r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f104,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f50,f78])).

fof(f78,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f100,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f92,f71,f98])).

fof(f92,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(superposition,[],[f83,f72])).

fof(f79,plain,
    ( spl6_5
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f74,f71,f77])).

fof(f74,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(superposition,[],[f40,f72])).

fof(f73,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f69,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f59,plain,
    ( spl6_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (25966)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.46  % (25958)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (25951)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (25947)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (25949)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (25952)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (25966)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  % (25975)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  fof(f2083,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f61,f65,f69,f73,f79,f100,f111,f115,f137,f175,f411,f416,f803,f1011,f1294,f1298,f1316,f1355,f1398,f1451,f1646,f1663,f1829,f1834,f1851,f1896,f2032,f2074,f2078,f2082])).
% 0.20/0.53  % (25969)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  fof(f2082,plain,(
% 0.20/0.53    k1_xboole_0 != k4_xboole_0(sK2,sK1) | sK1 != k4_xboole_0(sK1,sK3) | sK2 != k2_xboole_0(k4_xboole_0(sK2,sK1),sK1) | sK1 != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | sK1 = sK2),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f2078,plain,(
% 0.20/0.53    spl6_116 | ~spl6_112),
% 0.20/0.53    inference(avatar_split_clause,[],[f2064,f2030,f2076])).
% 0.20/0.53  fof(f2076,plain,(
% 0.20/0.53    spl6_116 <=> sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).
% 0.20/0.53  fof(f2030,plain,(
% 0.20/0.53    spl6_112 <=> sK1 = k4_xboole_0(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).
% 0.20/0.53  fof(f2064,plain,(
% 0.20/0.53    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK1),sK1) | ~spl6_112),
% 0.20/0.53    inference(superposition,[],[f55,f2031])).
% 0.20/0.53  fof(f2031,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(sK2,sK0) | ~spl6_112),
% 0.20/0.53    inference(avatar_component_clause,[],[f2030])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f47,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.20/0.53  fof(f2074,plain,(
% 0.20/0.53    spl6_115 | ~spl6_28 | ~spl6_112),
% 0.20/0.53    inference(avatar_split_clause,[],[f2073,f2030,f414,f2070])).
% 0.20/0.53  fof(f2070,plain,(
% 0.20/0.53    spl6_115 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).
% 0.20/0.53  fof(f414,plain,(
% 0.20/0.53    spl6_28 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.53  fof(f2073,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl6_28 | ~spl6_112)),
% 0.20/0.53    inference(forward_demodulation,[],[f2063,f415])).
% 0.20/0.53  fof(f415,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl6_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f414])).
% 0.20/0.53  fof(f2063,plain,(
% 0.20/0.53    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK2,sK1) | ~spl6_112),
% 0.20/0.53    inference(superposition,[],[f54,f2031])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f41,f43,f43])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.53  fof(f2032,plain,(
% 0.20/0.53    spl6_112 | ~spl6_38 | ~spl6_98 | ~spl6_101),
% 0.20/0.53    inference(avatar_split_clause,[],[f2028,f1874,f1827,f784,f2030])).
% 0.20/0.53  fof(f784,plain,(
% 0.20/0.53    spl6_38 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.20/0.53  fof(f1827,plain,(
% 0.20/0.53    spl6_98 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 0.20/0.53  fof(f1874,plain,(
% 0.20/0.53    spl6_101 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 0.20/0.53  fof(f2028,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(sK2,sK0) | (~spl6_38 | ~spl6_98 | ~spl6_101)),
% 0.20/0.53    inference(forward_demodulation,[],[f2027,f1875])).
% 0.20/0.53  fof(f1875,plain,(
% 0.20/0.53    sK2 = k2_xboole_0(sK1,sK2) | ~spl6_101),
% 0.20/0.53    inference(avatar_component_clause,[],[f1874])).
% 0.20/0.53  fof(f2027,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) | (~spl6_38 | ~spl6_98)),
% 0.20/0.53    inference(forward_demodulation,[],[f2026,f1828])).
% 0.20/0.53  fof(f1828,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(sK1,sK0) | ~spl6_98),
% 0.20/0.53    inference(avatar_component_clause,[],[f1827])).
% 0.20/0.53  fof(f2026,plain,(
% 0.20/0.53    k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k4_xboole_0(sK1,sK0) | ~spl6_38),
% 0.20/0.53    inference(forward_demodulation,[],[f1992,f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 0.20/0.53    inference(superposition,[],[f44,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.53  fof(f1992,plain,(
% 0.20/0.53    k4_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) | ~spl6_38),
% 0.20/0.53    inference(superposition,[],[f128,f785])).
% 0.20/0.53  fof(f785,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl6_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f784])).
% 0.20/0.53  fof(f1896,plain,(
% 0.20/0.53    spl6_101 | ~spl6_100),
% 0.20/0.53    inference(avatar_split_clause,[],[f1865,f1849,f1874])).
% 0.20/0.53  fof(f1849,plain,(
% 0.20/0.53    spl6_100 <=> sK2 = k2_xboole_0(sK2,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 0.20/0.53  fof(f1865,plain,(
% 0.20/0.53    sK2 = k2_xboole_0(sK1,sK2) | ~spl6_100),
% 0.20/0.53    inference(superposition,[],[f42,f1850])).
% 0.20/0.53  fof(f1850,plain,(
% 0.20/0.53    sK2 = k2_xboole_0(sK2,sK1) | ~spl6_100),
% 0.20/0.53    inference(avatar_component_clause,[],[f1849])).
% 0.20/0.53  fof(f1851,plain,(
% 0.20/0.53    spl6_100 | ~spl6_99),
% 0.20/0.53    inference(avatar_split_clause,[],[f1847,f1832,f1849])).
% 0.20/0.53  fof(f1832,plain,(
% 0.20/0.53    spl6_99 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 0.20/0.53  fof(f1847,plain,(
% 0.20/0.53    sK2 = k2_xboole_0(sK2,sK1) | ~spl6_99),
% 0.20/0.53    inference(forward_demodulation,[],[f1841,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.53  fof(f1841,plain,(
% 0.20/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) | ~spl6_99),
% 0.20/0.53    inference(superposition,[],[f45,f1833])).
% 0.20/0.53  fof(f1833,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl6_99),
% 0.20/0.53    inference(avatar_component_clause,[],[f1832])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.53  fof(f1834,plain,(
% 0.20/0.53    spl6_99 | ~spl6_78 | ~spl6_83),
% 0.20/0.53    inference(avatar_split_clause,[],[f1830,f1446,f1395,f1832])).
% 0.20/0.53  fof(f1395,plain,(
% 0.20/0.53    spl6_78 <=> sK1 = k4_xboole_0(sK1,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.20/0.53  fof(f1446,plain,(
% 0.20/0.53    spl6_83 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 0.20/0.53  fof(f1830,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(sK1,sK2) | (~spl6_78 | ~spl6_83)),
% 0.20/0.53    inference(forward_demodulation,[],[f1805,f103])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) )),
% 0.20/0.53    inference(resolution,[],[f50,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.20/0.53    inference(superposition,[],[f40,f42])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.20/0.53    inference(unused_predicate_definition_removal,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.53  fof(f1805,plain,(
% 0.20/0.53    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2) | (~spl6_78 | ~spl6_83)),
% 0.20/0.53    inference(superposition,[],[f1425,f1447])).
% 0.20/0.53  fof(f1447,plain,(
% 0.20/0.53    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) | ~spl6_83),
% 0.20/0.53    inference(avatar_component_clause,[],[f1446])).
% 0.20/0.53  fof(f1425,plain,(
% 0.20/0.53    ( ! [X3] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X3)) = k4_xboole_0(sK1,X3)) ) | ~spl6_78),
% 0.20/0.53    inference(superposition,[],[f51,f1396])).
% 0.20/0.53  fof(f1396,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(sK1,sK3) | ~spl6_78),
% 0.20/0.53    inference(avatar_component_clause,[],[f1395])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.53  fof(f1829,plain,(
% 0.20/0.53    spl6_98 | ~spl6_78 | ~spl6_94),
% 0.20/0.53    inference(avatar_split_clause,[],[f1825,f1661,f1395,f1827])).
% 0.20/0.53  fof(f1661,plain,(
% 0.20/0.53    spl6_94 <=> sK3 = k2_xboole_0(sK3,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 0.20/0.53  fof(f1825,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(sK1,sK0) | (~spl6_78 | ~spl6_94)),
% 0.20/0.53    inference(forward_demodulation,[],[f1804,f1396])).
% 0.20/0.53  fof(f1804,plain,(
% 0.20/0.53    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0) | (~spl6_78 | ~spl6_94)),
% 0.20/0.53    inference(superposition,[],[f1425,f1662])).
% 0.20/0.53  fof(f1662,plain,(
% 0.20/0.53    sK3 = k2_xboole_0(sK3,sK0) | ~spl6_94),
% 0.20/0.53    inference(avatar_component_clause,[],[f1661])).
% 0.20/0.53  % (25955)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  fof(f1663,plain,(
% 0.20/0.53    spl6_94 | ~spl6_93),
% 0.20/0.53    inference(avatar_split_clause,[],[f1659,f1644,f1661])).
% 0.20/0.54  fof(f1644,plain,(
% 0.20/0.54    spl6_93 <=> k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 0.20/0.54  fof(f1659,plain,(
% 0.20/0.54    sK3 = k2_xboole_0(sK3,sK0) | ~spl6_93),
% 0.20/0.54    inference(forward_demodulation,[],[f1654,f38])).
% 0.20/0.54  fof(f1654,plain,(
% 0.20/0.54    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k1_xboole_0) | ~spl6_93),
% 0.20/0.54    inference(superposition,[],[f45,f1645])).
% 0.20/0.54  fof(f1645,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK3) | ~spl6_93),
% 0.20/0.54    inference(avatar_component_clause,[],[f1644])).
% 0.20/0.54  fof(f1646,plain,(
% 0.20/0.54    spl6_93 | ~spl6_4 | ~spl6_74),
% 0.20/0.54    inference(avatar_split_clause,[],[f1642,f1352,f71,f1644])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    spl6_4 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.54  fof(f1352,plain,(
% 0.20/0.54    spl6_74 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 0.20/0.54  fof(f1642,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK3) | (~spl6_4 | ~spl6_74)),
% 0.20/0.54    inference(forward_demodulation,[],[f1627,f102])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(resolution,[],[f50,f40])).
% 0.20/0.54  fof(f1627,plain,(
% 0.20/0.54    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3) | (~spl6_4 | ~spl6_74)),
% 0.20/0.54    inference(superposition,[],[f1376,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) | ~spl6_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f71])).
% 0.20/0.54  fof(f1376,plain,(
% 0.20/0.54    ( ! [X3] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X3)) = k4_xboole_0(sK0,X3)) ) | ~spl6_74),
% 0.20/0.54    inference(superposition,[],[f51,f1353])).
% 0.20/0.54  fof(f1353,plain,(
% 0.20/0.54    sK0 = k4_xboole_0(sK0,sK2) | ~spl6_74),
% 0.20/0.54    inference(avatar_component_clause,[],[f1352])).
% 0.20/0.54  fof(f1451,plain,(
% 0.20/0.54    spl6_83 | ~spl6_73),
% 0.20/0.54    inference(avatar_split_clause,[],[f1435,f1314,f1446])).
% 0.20/0.54  fof(f1314,plain,(
% 0.20/0.54    spl6_73 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 0.20/0.54  fof(f1435,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) | ~spl6_73),
% 0.20/0.54    inference(superposition,[],[f45,f1315])).
% 0.20/0.54  fof(f1315,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) | ~spl6_73),
% 0.20/0.54    inference(avatar_component_clause,[],[f1314])).
% 0.20/0.54  fof(f1398,plain,(
% 0.20/0.54    spl6_78 | ~spl6_71),
% 0.20/0.54    inference(avatar_split_clause,[],[f1383,f1296,f1395])).
% 0.20/0.54  % (25956)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  fof(f1296,plain,(
% 0.20/0.54    spl6_71 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 0.20/0.54  fof(f1383,plain,(
% 0.20/0.54    sK1 = k4_xboole_0(sK1,sK3) | ~spl6_71),
% 0.20/0.54    inference(superposition,[],[f80,f1297])).
% 0.20/0.54  fof(f1297,plain,(
% 0.20/0.54    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | ~spl6_71),
% 0.20/0.54    inference(avatar_component_clause,[],[f1296])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.54    inference(superposition,[],[f42,f38])).
% 0.20/0.54  % (25976)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  fof(f1355,plain,(
% 0.20/0.54    spl6_74 | ~spl6_70),
% 0.20/0.54    inference(avatar_split_clause,[],[f1340,f1292,f1352])).
% 0.20/0.54  fof(f1292,plain,(
% 0.20/0.54    spl6_70 <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 0.20/0.54  fof(f1340,plain,(
% 0.20/0.54    sK0 = k4_xboole_0(sK0,sK2) | ~spl6_70),
% 0.20/0.54    inference(superposition,[],[f80,f1293])).
% 0.20/0.54  fof(f1293,plain,(
% 0.20/0.54    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) | ~spl6_70),
% 0.20/0.54    inference(avatar_component_clause,[],[f1292])).
% 0.20/0.54  fof(f1316,plain,(
% 0.20/0.54    spl6_73 | ~spl6_9 | ~spl6_53),
% 0.20/0.54    inference(avatar_split_clause,[],[f1312,f977,f135,f1314])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    spl6_9 <=> k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.54  fof(f977,plain,(
% 0.20/0.54    spl6_53 <=> sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.20/0.54  fof(f1312,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) | (~spl6_9 | ~spl6_53)),
% 0.20/0.54    inference(forward_demodulation,[],[f1252,f978])).
% 0.20/0.54  % (25961)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  fof(f978,plain,(
% 0.20/0.54    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) | ~spl6_53),
% 0.20/0.54    inference(avatar_component_clause,[],[f977])).
% 0.20/0.54  fof(f1252,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3)) | ~spl6_9),
% 0.20/0.54    inference(superposition,[],[f55,f136])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl6_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f135])).
% 0.20/0.54  fof(f1298,plain,(
% 0.20/0.54    spl6_71 | ~spl6_27),
% 0.20/0.54    inference(avatar_split_clause,[],[f1240,f409,f1296])).
% 0.20/0.54  fof(f409,plain,(
% 0.20/0.54    spl6_27 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.54  fof(f1240,plain,(
% 0.20/0.54    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) | ~spl6_27),
% 0.20/0.54    inference(superposition,[],[f55,f410])).
% 0.20/0.54  fof(f410,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl6_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f409])).
% 0.20/0.54  fof(f1294,plain,(
% 0.20/0.54    spl6_70 | ~spl6_28),
% 0.20/0.54    inference(avatar_split_clause,[],[f1239,f414,f1292])).
% 0.20/0.54  fof(f1239,plain,(
% 0.20/0.54    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) | ~spl6_28),
% 0.20/0.54    inference(superposition,[],[f55,f415])).
% 0.20/0.54  fof(f1011,plain,(
% 0.20/0.54    spl6_53 | ~spl6_8 | ~spl6_9),
% 0.20/0.54    inference(avatar_split_clause,[],[f1010,f135,f113,f977])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    spl6_8 <=> k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.54  fof(f1010,plain,(
% 0.20/0.54    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) | (~spl6_8 | ~spl6_9)),
% 0.20/0.54    inference(forward_demodulation,[],[f1009,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.54  fof(f1009,plain,(
% 0.20/0.54    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k1_xboole_0) | (~spl6_8 | ~spl6_9)),
% 0.20/0.54    inference(forward_demodulation,[],[f946,f114])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f113])).
% 0.20/0.54  fof(f946,plain,(
% 0.20/0.54    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) | ~spl6_9),
% 0.20/0.54    inference(superposition,[],[f54,f136])).
% 0.20/0.54  fof(f803,plain,(
% 0.20/0.54    spl6_38 | ~spl6_11),
% 0.20/0.54    inference(avatar_split_clause,[],[f750,f173,f784])).
% 0.20/0.54  fof(f173,plain,(
% 0.20/0.54    spl6_11 <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.54  fof(f750,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl6_11),
% 0.20/0.54    inference(superposition,[],[f174,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) | ~spl6_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f173])).
% 0.20/0.54  fof(f416,plain,(
% 0.20/0.54    spl6_28 | ~spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f412,f67,f414])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    spl6_3 <=> r1_xboole_0(sK2,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.54  % (25950)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  fof(f412,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f406,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.54  fof(f406,plain,(
% 0.20/0.54    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ) | ~spl6_3),
% 0.20/0.54    inference(forward_demodulation,[],[f404,f54])).
% 0.20/0.54  fof(f404,plain,(
% 0.20/0.54    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) ) | ~spl6_3),
% 0.20/0.54    inference(resolution,[],[f56,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    r1_xboole_0(sK2,sK0) | ~spl6_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f67])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f49,f43])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.54  fof(f411,plain,(
% 0.20/0.54    spl6_27 | ~spl6_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f407,f63,f409])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl6_2 <=> r1_xboole_0(sK3,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.54  fof(f407,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl6_2),
% 0.20/0.54    inference(resolution,[],[f405,f39])).
% 0.20/0.54  fof(f405,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) ) | ~spl6_2),
% 0.20/0.54    inference(forward_demodulation,[],[f403,f54])).
% 0.20/0.54  fof(f403,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) ) | ~spl6_2),
% 0.20/0.54    inference(resolution,[],[f56,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    r1_xboole_0(sK3,sK1) | ~spl6_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f63])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    spl6_11 | ~spl6_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f171,f109,f173])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    spl6_7 <=> k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) | ~spl6_7),
% 0.20/0.54    inference(forward_demodulation,[],[f149,f38])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) | ~spl6_7),
% 0.20/0.54    inference(superposition,[],[f45,f110])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f109])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    spl6_9 | ~spl6_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f127,f71,f135])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl6_4),
% 0.20/0.54    inference(superposition,[],[f44,f72])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    spl6_8 | ~spl6_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f105,f98,f113])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    spl6_6 <=> r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_6),
% 0.20/0.54    inference(resolution,[],[f50,f99])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f98])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    spl6_7 | ~spl6_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f104,f77,f109])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    spl6_5 <=> r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_5),
% 0.20/0.54    inference(resolution,[],[f50,f78])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f77])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    spl6_6 | ~spl6_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f92,f71,f98])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) | ~spl6_4),
% 0.20/0.54    inference(superposition,[],[f83,f72])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    spl6_5 | ~spl6_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f74,f71,f77])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | ~spl6_4),
% 0.20/0.54    inference(superposition,[],[f40,f72])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    spl6_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f32,f71])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 0.20/0.54    inference(flattening,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.20/0.54    inference(negated_conjecture,[],[f17])).
% 0.20/0.54  fof(f17,conjecture,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    spl6_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f33,f67])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    r1_xboole_0(sK2,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    spl6_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f34,f63])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    r1_xboole_0(sK3,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ~spl6_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f35,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    spl6_1 <=> sK1 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    sK1 != sK2),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (25966)------------------------------
% 0.20/0.54  % (25966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25966)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (25966)Memory used [KB]: 12153
% 0.20/0.54  % (25966)Time elapsed: 0.143 s
% 0.20/0.54  % (25966)------------------------------
% 0.20/0.54  % (25966)------------------------------
% 0.20/0.54  % (25973)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.54  % (25968)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.54  % (25946)Success in time 0.19 s
%------------------------------------------------------------------------------
