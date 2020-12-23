%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:39 EST 2020

% Result     : Theorem 3.22s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  280 ( 560 expanded)
%              Number of leaves         :   67 ( 242 expanded)
%              Depth                    :   14
%              Number of atoms          :  730 (1345 expanded)
%              Number of equality atoms :  146 ( 292 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2416,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f114,f146,f153,f156,f173,f263,f284,f295,f305,f313,f408,f416,f513,f526,f605,f618,f757,f781,f835,f1252,f1374,f1379,f1489,f1498,f1571,f1631,f1726,f1815,f1847,f1880,f1904,f1948,f2223,f2322,f2344,f2401,f2414,f2415])).

fof(f2415,plain,
    ( k1_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | sK1 != k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2414,plain,
    ( spl2_182
    | ~ spl2_114
    | ~ spl2_149 ),
    inference(avatar_split_clause,[],[f1959,f1902,f1496,f2412])).

fof(f2412,plain,
    ( spl2_182
  <=> k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_182])])).

fof(f1496,plain,
    ( spl2_114
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).

fof(f1902,plain,
    ( spl2_149
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).

fof(f1959,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_114
    | ~ spl2_149 ),
    inference(forward_demodulation,[],[f1958,f1497])).

fof(f1497,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_114 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f1958,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_149 ),
    inference(forward_demodulation,[],[f1956,f100])).

fof(f100,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1956,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_149 ),
    inference(superposition,[],[f83,f1903])).

fof(f1903,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_149 ),
    inference(avatar_component_clause,[],[f1902])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2401,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2344,plain,
    ( spl2_176
    | ~ spl2_14
    | ~ spl2_173 ),
    inference(avatar_split_clause,[],[f2336,f2320,f261,f2342])).

fof(f2342,plain,
    ( spl2_176
  <=> sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).

fof(f261,plain,
    ( spl2_14
  <=> sK1 = k3_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f2320,plain,
    ( spl2_173
  <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).

fof(f2336,plain,
    ( sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_173 ),
    inference(forward_demodulation,[],[f2335,f262])).

fof(f262,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f261])).

fof(f2335,plain,
    ( k3_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_173 ),
    inference(forward_demodulation,[],[f2331,f83])).

fof(f2331,plain,
    ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl2_173 ),
    inference(superposition,[],[f83,f2321])).

fof(f2321,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_173 ),
    inference(avatar_component_clause,[],[f2320])).

fof(f2322,plain,
    ( spl2_173
    | ~ spl2_26
    | ~ spl2_113
    | ~ spl2_122
    | ~ spl2_125
    | ~ spl2_144
    | ~ spl2_147 ),
    inference(avatar_split_clause,[],[f2002,f1878,f1845,f1629,f1569,f1487,f311,f2320])).

fof(f311,plain,
    ( spl2_26
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1487,plain,
    ( spl2_113
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).

fof(f1569,plain,
    ( spl2_122
  <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).

fof(f1629,plain,
    ( spl2_125
  <=> k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).

fof(f1845,plain,
    ( spl2_144
  <=> m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).

fof(f1878,plain,
    ( spl2_147
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).

fof(f2002,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_26
    | ~ spl2_113
    | ~ spl2_122
    | ~ spl2_125
    | ~ spl2_144
    | ~ spl2_147 ),
    inference(forward_demodulation,[],[f1994,f1896])).

fof(f1896,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_122
    | ~ spl2_125
    | ~ spl2_144
    | ~ spl2_147 ),
    inference(forward_demodulation,[],[f1887,f1867])).

fof(f1867,plain,
    ( k4_xboole_0(sK1,sK1) = k3_subset_1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_122
    | ~ spl2_125
    | ~ spl2_144 ),
    inference(forward_demodulation,[],[f1859,f1866])).

fof(f1866,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl2_122
    | ~ spl2_125
    | ~ spl2_144 ),
    inference(forward_demodulation,[],[f1856,f1717])).

fof(f1717,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl2_122
    | ~ spl2_125 ),
    inference(forward_demodulation,[],[f1716,f1630])).

fof(f1630,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_125 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1716,plain,
    ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl2_122 ),
    inference(forward_demodulation,[],[f1712,f100])).

fof(f1712,plain,
    ( k3_xboole_0(k1_tops_1(sK0,sK1),sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl2_122 ),
    inference(superposition,[],[f83,f1570])).

fof(f1570,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_122 ),
    inference(avatar_component_clause,[],[f1569])).

fof(f1856,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) = k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1))
    | ~ spl2_144 ),
    inference(resolution,[],[f1846,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1846,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl2_144 ),
    inference(avatar_component_clause,[],[f1845])).

fof(f1859,plain,
    ( k4_xboole_0(sK1,sK1) = k3_subset_1(k1_tops_1(sK0,sK1),k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)))
    | ~ spl2_144 ),
    inference(resolution,[],[f1846,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1887,plain,
    ( k3_subset_1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_147 ),
    inference(resolution,[],[f1879,f80])).

fof(f1879,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl2_147 ),
    inference(avatar_component_clause,[],[f1878])).

fof(f1994,plain,
    ( k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_26
    | ~ spl2_113 ),
    inference(superposition,[],[f506,f1488])).

fof(f1488,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_113 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f506,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X0)) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)
    | ~ spl2_26 ),
    inference(superposition,[],[f79,f312])).

fof(f312,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f311])).

fof(f79,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2223,plain,
    ( spl2_165
    | ~ spl2_44
    | ~ spl2_150 ),
    inference(avatar_split_clause,[],[f1978,f1946,f616,f2221])).

fof(f2221,plain,
    ( spl2_165
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_165])])).

fof(f616,plain,
    ( spl2_44
  <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1946,plain,
    ( spl2_150
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_150])])).

fof(f1978,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_44
    | ~ spl2_150 ),
    inference(forward_demodulation,[],[f1973,f617])).

fof(f617,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f616])).

fof(f1973,plain,
    ( k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_150 ),
    inference(resolution,[],[f1947,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1947,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_150 ),
    inference(avatar_component_clause,[],[f1946])).

fof(f1948,plain,
    ( spl2_150
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_107
    | ~ spl2_135 ),
    inference(avatar_split_clause,[],[f1935,f1724,f1377,f148,f112,f108,f1946])).

fof(f108,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f112,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f148,plain,
    ( spl2_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1377,plain,
    ( spl2_107
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f1724,plain,
    ( spl2_135
  <=> sK1 = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f1935,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_107
    | ~ spl2_135 ),
    inference(forward_demodulation,[],[f1934,f1725])).

fof(f1725,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl2_135 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f1934,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_107
    | ~ spl2_135 ),
    inference(forward_demodulation,[],[f1933,f1725])).

fof(f1933,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1))))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_107
    | ~ spl2_135 ),
    inference(subsumption_resolution,[],[f1932,f102])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1932,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1))))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_107
    | ~ spl2_135 ),
    inference(forward_demodulation,[],[f1931,f1725])).

fof(f1931,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1))))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_107
    | ~ spl2_135 ),
    inference(forward_demodulation,[],[f1911,f1725])).

fof(f1911,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)))
    | r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1))))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_107 ),
    inference(resolution,[],[f1907,f1378])).

fof(f1378,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_107 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1907,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f139,f149])).

fof(f149,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f121,f109])).

fof(f109,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1904,plain,
    ( spl2_149
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f1873,f414,f151,f1902])).

fof(f151,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f414,plain,
    ( spl2_30
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1873,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_6
    | ~ spl2_30 ),
    inference(superposition,[],[f462,f152])).

fof(f152,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f462,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)
    | ~ spl2_30 ),
    inference(resolution,[],[f415,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f415,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f414])).

fof(f1880,plain,
    ( spl2_147
    | ~ spl2_122
    | ~ spl2_125
    | ~ spl2_144 ),
    inference(avatar_split_clause,[],[f1868,f1845,f1629,f1569,f1878])).

fof(f1868,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl2_122
    | ~ spl2_125
    | ~ spl2_144 ),
    inference(forward_demodulation,[],[f1860,f1866])).

fof(f1860,plain,
    ( m1_subset_1(k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl2_144 ),
    inference(resolution,[],[f1846,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1847,plain,
    ( spl2_144
    | ~ spl2_141 ),
    inference(avatar_split_clause,[],[f1824,f1813,f1845])).

fof(f1813,plain,
    ( spl2_141
  <=> r1_tarski(k4_xboole_0(sK1,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).

fof(f1824,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))
    | ~ spl2_141 ),
    inference(resolution,[],[f1814,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1814,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_141 ),
    inference(avatar_component_clause,[],[f1813])).

fof(f1815,plain,
    ( spl2_141
    | ~ spl2_122 ),
    inference(avatar_split_clause,[],[f1709,f1569,f1813])).

fof(f1709,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_122 ),
    inference(superposition,[],[f84,f1570])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1726,plain,
    ( spl2_135
    | ~ spl2_44
    | ~ spl2_122 ),
    inference(avatar_split_clause,[],[f1714,f1569,f616,f1724])).

fof(f1714,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl2_44
    | ~ spl2_122 ),
    inference(forward_demodulation,[],[f1713,f617])).

fof(f1713,plain,
    ( k2_xboole_0(sK1,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_122 ),
    inference(forward_demodulation,[],[f1710,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1710,plain,
    ( k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | ~ spl2_122 ),
    inference(superposition,[],[f82,f1570])).

fof(f1631,plain,
    ( spl2_125
    | ~ spl2_96 ),
    inference(avatar_split_clause,[],[f1365,f1250,f1629])).

fof(f1250,plain,
    ( spl2_96
  <=> k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f1365,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_96 ),
    inference(superposition,[],[f1251,f100])).

fof(f1251,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f1250])).

fof(f1571,plain,
    ( spl2_122
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f614,f603,f1569])).

fof(f603,plain,
    ( spl2_42
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f614,plain,
    ( k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_42 ),
    inference(superposition,[],[f81,f604])).

fof(f604,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f603])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1498,plain,
    ( spl2_114
    | ~ spl2_26
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f546,f524,f311,f1496])).

fof(f524,plain,
    ( spl2_36
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f546,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_26
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f545,f312])).

fof(f545,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_36 ),
    inference(superposition,[],[f81,f525])).

fof(f525,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f524])).

fof(f1489,plain,
    ( spl2_113
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f509,f311,f293,f171,f112,f1487])).

fof(f171,plain,
    ( spl2_9
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f293,plain,
    ( spl2_22
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f509,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_22
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f508,f317])).

fof(f317,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f315,f294])).

fof(f294,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f293])).

fof(f315,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f129,f172])).

fof(f172,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f129,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(sK1,X5) = k4_subset_1(u1_struct_0(sK0),sK1,X5) )
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f508,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f505,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f505,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(superposition,[],[f82,f312])).

fof(f1379,plain,
    ( spl2_107
    | ~ spl2_3
    | ~ spl2_28
    | ~ spl2_106 ),
    inference(avatar_split_clause,[],[f1375,f1372,f406,f112,f1377])).

fof(f406,plain,
    ( spl2_28
  <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1372,plain,
    ( spl2_106
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).

fof(f1375,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_28
    | ~ spl2_106 ),
    inference(forward_demodulation,[],[f1373,f419])).

fof(f419,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK1))
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(resolution,[],[f407,f129])).

fof(f407,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f406])).

fof(f1373,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_106 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1374,plain,
    ( spl2_106
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f418,f406,f112,f1372])).

fof(f418,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(resolution,[],[f407,f130])).

fof(f130,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X6),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1252,plain,
    ( spl2_96
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f518,f511,f1250])).

fof(f511,plain,
    ( spl2_34
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f518,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_34 ),
    inference(resolution,[],[f512,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f512,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f511])).

fof(f835,plain,
    ( spl2_60
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_58 ),
    inference(avatar_split_clause,[],[f815,f779,f108,f104,f833])).

fof(f833,plain,
    ( spl2_60
  <=> v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f104,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f779,plain,
    ( spl2_58
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f815,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f814,f105])).

fof(f105,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f814,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl2_2
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f795,f109])).

fof(f795,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl2_58 ),
    inference(resolution,[],[f780,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f780,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f779])).

fof(f781,plain,
    ( spl2_58
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f772,f755,f779])).

fof(f755,plain,
    ( spl2_56
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f772,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_56 ),
    inference(resolution,[],[f756,f92])).

fof(f756,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f755])).

fof(f757,plain,
    ( spl2_56
    | ~ spl2_4
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f753,f511,f144,f755])).

fof(f144,plain,
    ( spl2_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f753,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_34 ),
    inference(resolution,[],[f522,f145])).

fof(f145,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f522,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl2_34 ),
    inference(resolution,[],[f512,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f618,plain,
    ( spl2_44
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f610,f603,f616])).

fof(f610,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_42 ),
    inference(superposition,[],[f604,f99])).

fof(f605,plain,
    ( spl2_42
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f519,f511,f603])).

fof(f519,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_34 ),
    inference(resolution,[],[f512,f97])).

fof(f526,plain,
    ( spl2_36
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f317,f293,f171,f112,f524])).

fof(f513,plain,
    ( spl2_34
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f504,f311,f511])).

fof(f504,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_26 ),
    inference(superposition,[],[f84,f312])).

fof(f416,plain,
    ( spl2_30
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f354,f293,f171,f112,f414])).

fof(f354,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f350,f294])).

fof(f350,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f130,f172])).

fof(f408,plain,
    ( spl2_28
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f353,f112,f406])).

fof(f353,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f349,f314])).

fof(f314,plain,
    ( k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f129,f113])).

fof(f349,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f130,f113])).

fof(f313,plain,
    ( spl2_26
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f296,f282,f112,f311])).

fof(f282,plain,
    ( spl2_19
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f296,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(superposition,[],[f283,f122])).

fof(f122,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f70])).

fof(f283,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f282])).

fof(f305,plain,
    ( spl2_24
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f132,f112,f108,f303])).

fof(f303,plain,
    ( spl2_24
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f132,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f115,f109])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f295,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f134,f112,f108,f293])).

fof(f134,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f117,f109])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f284,plain,
    ( spl2_19
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f133,f112,f108,f282])).

fof(f133,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f116,f109])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f263,plain,
    ( spl2_14
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f258,f112,f261])).

fof(f258,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ spl2_3 ),
    inference(superposition,[],[f125,f126])).

fof(f126,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,X4) = X4
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f125,plain,
    ( ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,sK1) = k3_xboole_0(X3,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f173,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f135,f112,f108,f171])).

fof(f135,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f118,f109])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f156,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f154,f151,f148])).

fof(f154,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f66,f152])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f153,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f65,f151,f148])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f146,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f131,f112,f144])).

fof(f131,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f113,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f114,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f67,f112])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f69,f108])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f68,f104])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:03:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (2811)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (2797)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (2803)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (2794)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (2796)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (2790)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (2788)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (2793)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (2789)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (2813)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (2791)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (2799)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (2817)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (2807)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (2806)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (2818)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (2792)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (2805)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (2816)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (2808)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (2800)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (2802)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (2798)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (2795)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (2815)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (2814)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (2812)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.57  % (2809)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.58  % (2804)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.82/0.60  % (2810)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 3.22/0.81  % (2815)Refutation found. Thanks to Tanya!
% 3.22/0.81  % SZS status Theorem for theBenchmark
% 3.22/0.81  % SZS output start Proof for theBenchmark
% 3.22/0.81  fof(f2416,plain,(
% 3.22/0.81    $false),
% 3.22/0.81    inference(avatar_sat_refutation,[],[f106,f110,f114,f146,f153,f156,f173,f263,f284,f295,f305,f313,f408,f416,f513,f526,f605,f618,f757,f781,f835,f1252,f1374,f1379,f1489,f1498,f1571,f1631,f1726,f1815,f1847,f1880,f1904,f1948,f2223,f2322,f2344,f2401,f2414,f2415])).
% 3.22/0.81  fof(f2415,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) != k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | sK1 != k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)),
% 3.22/0.81    introduced(theory_tautology_sat_conflict,[])).
% 3.22/0.81  fof(f2414,plain,(
% 3.22/0.81    spl2_182 | ~spl2_114 | ~spl2_149),
% 3.22/0.81    inference(avatar_split_clause,[],[f1959,f1902,f1496,f2412])).
% 3.22/0.81  fof(f2412,plain,(
% 3.22/0.81    spl2_182 <=> k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_182])])).
% 3.22/0.81  fof(f1496,plain,(
% 3.22/0.81    spl2_114 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_114])])).
% 3.22/0.81  fof(f1902,plain,(
% 3.22/0.81    spl2_149 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_149])])).
% 3.22/0.81  fof(f1959,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_114 | ~spl2_149)),
% 3.22/0.81    inference(forward_demodulation,[],[f1958,f1497])).
% 3.22/0.81  fof(f1497,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_114),
% 3.22/0.81    inference(avatar_component_clause,[],[f1496])).
% 3.22/0.81  fof(f1958,plain,(
% 3.22/0.81    k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_149),
% 3.22/0.81    inference(forward_demodulation,[],[f1956,f100])).
% 3.22/0.81  fof(f100,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f2])).
% 3.22/0.81  fof(f2,axiom,(
% 3.22/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.22/0.81  fof(f1956,plain,(
% 3.22/0.81    k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_149),
% 3.22/0.81    inference(superposition,[],[f83,f1903])).
% 3.22/0.81  fof(f1903,plain,(
% 3.22/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_149),
% 3.22/0.81    inference(avatar_component_clause,[],[f1902])).
% 3.22/0.81  fof(f83,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f13])).
% 3.22/0.81  fof(f13,axiom,(
% 3.22/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.22/0.81  fof(f2401,plain,(
% 3.22/0.81    sK1 != k1_tops_1(sK0,sK1) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.22/0.81    introduced(theory_tautology_sat_conflict,[])).
% 3.22/0.81  fof(f2344,plain,(
% 3.22/0.81    spl2_176 | ~spl2_14 | ~spl2_173),
% 3.22/0.81    inference(avatar_split_clause,[],[f2336,f2320,f261,f2342])).
% 3.22/0.81  fof(f2342,plain,(
% 3.22/0.81    spl2_176 <=> sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_176])])).
% 3.22/0.81  fof(f261,plain,(
% 3.22/0.81    spl2_14 <=> sK1 = k3_xboole_0(sK1,sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 3.22/0.81  fof(f2320,plain,(
% 3.22/0.81    spl2_173 <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_173])])).
% 3.22/0.81  fof(f2336,plain,(
% 3.22/0.81    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_14 | ~spl2_173)),
% 3.22/0.81    inference(forward_demodulation,[],[f2335,f262])).
% 3.22/0.81  fof(f262,plain,(
% 3.22/0.81    sK1 = k3_xboole_0(sK1,sK1) | ~spl2_14),
% 3.22/0.81    inference(avatar_component_clause,[],[f261])).
% 3.22/0.81  fof(f2335,plain,(
% 3.22/0.81    k3_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_173),
% 3.22/0.81    inference(forward_demodulation,[],[f2331,f83])).
% 3.22/0.81  fof(f2331,plain,(
% 3.22/0.81    k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | ~spl2_173),
% 3.22/0.81    inference(superposition,[],[f83,f2321])).
% 3.22/0.81  fof(f2321,plain,(
% 3.22/0.81    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_173),
% 3.22/0.81    inference(avatar_component_clause,[],[f2320])).
% 3.22/0.81  fof(f2322,plain,(
% 3.22/0.81    spl2_173 | ~spl2_26 | ~spl2_113 | ~spl2_122 | ~spl2_125 | ~spl2_144 | ~spl2_147),
% 3.22/0.81    inference(avatar_split_clause,[],[f2002,f1878,f1845,f1629,f1569,f1487,f311,f2320])).
% 3.22/0.81  fof(f311,plain,(
% 3.22/0.81    spl2_26 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 3.22/0.81  fof(f1487,plain,(
% 3.22/0.81    spl2_113 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).
% 3.22/0.81  fof(f1569,plain,(
% 3.22/0.81    spl2_122 <=> k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).
% 3.22/0.81  fof(f1629,plain,(
% 3.22/0.81    spl2_125 <=> k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).
% 3.22/0.81  fof(f1845,plain,(
% 3.22/0.81    spl2_144 <=> m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).
% 3.22/0.81  fof(f1878,plain,(
% 3.22/0.81    spl2_147 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_147])])).
% 3.22/0.81  fof(f2002,plain,(
% 3.22/0.81    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_26 | ~spl2_113 | ~spl2_122 | ~spl2_125 | ~spl2_144 | ~spl2_147)),
% 3.22/0.81    inference(forward_demodulation,[],[f1994,f1896])).
% 3.22/0.81  fof(f1896,plain,(
% 3.22/0.81    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_122 | ~spl2_125 | ~spl2_144 | ~spl2_147)),
% 3.22/0.81    inference(forward_demodulation,[],[f1887,f1867])).
% 3.22/0.81  fof(f1867,plain,(
% 3.22/0.81    k4_xboole_0(sK1,sK1) = k3_subset_1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_122 | ~spl2_125 | ~spl2_144)),
% 3.22/0.81    inference(forward_demodulation,[],[f1859,f1866])).
% 3.22/0.81  fof(f1866,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) | (~spl2_122 | ~spl2_125 | ~spl2_144)),
% 3.22/0.81    inference(forward_demodulation,[],[f1856,f1717])).
% 3.22/0.81  fof(f1717,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) | (~spl2_122 | ~spl2_125)),
% 3.22/0.81    inference(forward_demodulation,[],[f1716,f1630])).
% 3.22/0.81  fof(f1630,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_125),
% 3.22/0.81    inference(avatar_component_clause,[],[f1629])).
% 3.22/0.81  fof(f1716,plain,(
% 3.22/0.81    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) | ~spl2_122),
% 3.22/0.81    inference(forward_demodulation,[],[f1712,f100])).
% 3.22/0.81  fof(f1712,plain,(
% 3.22/0.81    k3_xboole_0(k1_tops_1(sK0,sK1),sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) | ~spl2_122),
% 3.22/0.81    inference(superposition,[],[f83,f1570])).
% 3.22/0.81  fof(f1570,plain,(
% 3.22/0.81    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_122),
% 3.22/0.81    inference(avatar_component_clause,[],[f1569])).
% 3.22/0.81  fof(f1856,plain,(
% 3.22/0.81    k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) = k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)) | ~spl2_144),
% 3.22/0.81    inference(resolution,[],[f1846,f80])).
% 3.22/0.81  fof(f80,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f52])).
% 3.22/0.81  fof(f52,plain,(
% 3.22/0.81    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f15])).
% 3.22/0.81  fof(f15,axiom,(
% 3.22/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.22/0.81  fof(f1846,plain,(
% 3.22/0.81    m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) | ~spl2_144),
% 3.22/0.81    inference(avatar_component_clause,[],[f1845])).
% 3.22/0.81  fof(f1859,plain,(
% 3.22/0.81    k4_xboole_0(sK1,sK1) = k3_subset_1(k1_tops_1(sK0,sK1),k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1))) | ~spl2_144),
% 3.22/0.81    inference(resolution,[],[f1846,f87])).
% 3.22/0.81  fof(f87,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 3.22/0.81    inference(cnf_transformation,[],[f55])).
% 3.22/0.81  fof(f55,plain,(
% 3.22/0.81    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f20])).
% 3.22/0.81  fof(f20,axiom,(
% 3.22/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.22/0.81  fof(f1887,plain,(
% 3.22/0.81    k3_subset_1(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_147),
% 3.22/0.81    inference(resolution,[],[f1879,f80])).
% 3.22/0.81  fof(f1879,plain,(
% 3.22/0.81    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) | ~spl2_147),
% 3.22/0.81    inference(avatar_component_clause,[],[f1878])).
% 3.22/0.81  fof(f1994,plain,(
% 3.22/0.81    k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_26 | ~spl2_113)),
% 3.22/0.81    inference(superposition,[],[f506,f1488])).
% 3.22/0.81  fof(f1488,plain,(
% 3.22/0.81    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_113),
% 3.22/0.81    inference(avatar_component_clause,[],[f1487])).
% 3.22/0.81  fof(f506,plain,(
% 3.22/0.81    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X0)) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)) ) | ~spl2_26),
% 3.22/0.81    inference(superposition,[],[f79,f312])).
% 3.22/0.81  fof(f312,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_26),
% 3.22/0.81    inference(avatar_component_clause,[],[f311])).
% 3.22/0.81  fof(f79,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f12])).
% 3.22/0.81  fof(f12,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.22/0.81  fof(f2223,plain,(
% 3.22/0.81    spl2_165 | ~spl2_44 | ~spl2_150),
% 3.22/0.81    inference(avatar_split_clause,[],[f1978,f1946,f616,f2221])).
% 3.22/0.81  fof(f2221,plain,(
% 3.22/0.81    spl2_165 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_165])])).
% 3.22/0.81  fof(f616,plain,(
% 3.22/0.81    spl2_44 <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 3.22/0.81  fof(f1946,plain,(
% 3.22/0.81    spl2_150 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_150])])).
% 3.22/0.81  fof(f1978,plain,(
% 3.22/0.81    sK1 = k1_tops_1(sK0,sK1) | (~spl2_44 | ~spl2_150)),
% 3.22/0.81    inference(forward_demodulation,[],[f1973,f617])).
% 3.22/0.81  fof(f617,plain,(
% 3.22/0.81    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_44),
% 3.22/0.81    inference(avatar_component_clause,[],[f616])).
% 3.22/0.81  fof(f1973,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_150),
% 3.22/0.81    inference(resolution,[],[f1947,f97])).
% 3.22/0.81  fof(f97,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.22/0.81    inference(cnf_transformation,[],[f63])).
% 3.22/0.81  fof(f63,plain,(
% 3.22/0.81    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.22/0.81    inference(ennf_transformation,[],[f6])).
% 3.22/0.81  fof(f6,axiom,(
% 3.22/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.22/0.81  fof(f1947,plain,(
% 3.22/0.81    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_150),
% 3.22/0.81    inference(avatar_component_clause,[],[f1946])).
% 3.22/0.81  fof(f1948,plain,(
% 3.22/0.81    spl2_150 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_107 | ~spl2_135),
% 3.22/0.81    inference(avatar_split_clause,[],[f1935,f1724,f1377,f148,f112,f108,f1946])).
% 3.22/0.81  fof(f108,plain,(
% 3.22/0.81    spl2_2 <=> l1_pre_topc(sK0)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.22/0.81  fof(f112,plain,(
% 3.22/0.81    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.22/0.81  fof(f148,plain,(
% 3.22/0.81    spl2_5 <=> v3_pre_topc(sK1,sK0)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.22/0.81  fof(f1377,plain,(
% 3.22/0.81    spl2_107 <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).
% 3.22/0.81  fof(f1724,plain,(
% 3.22/0.81    spl2_135 <=> sK1 = k2_xboole_0(sK1,sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 3.22/0.81  fof(f1935,plain,(
% 3.22/0.81    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_107 | ~spl2_135)),
% 3.22/0.81    inference(forward_demodulation,[],[f1934,f1725])).
% 3.22/0.81  fof(f1725,plain,(
% 3.22/0.81    sK1 = k2_xboole_0(sK1,sK1) | ~spl2_135),
% 3.22/0.81    inference(avatar_component_clause,[],[f1724])).
% 3.22/0.81  fof(f1934,plain,(
% 3.22/0.81    r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_107 | ~spl2_135)),
% 3.22/0.81    inference(forward_demodulation,[],[f1933,f1725])).
% 3.22/0.81  fof(f1933,plain,(
% 3.22/0.81    r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)))) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_107 | ~spl2_135)),
% 3.22/0.81    inference(subsumption_resolution,[],[f1932,f102])).
% 3.22/0.81  fof(f102,plain,(
% 3.22/0.81    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.22/0.81    inference(equality_resolution,[],[f94])).
% 3.22/0.81  fof(f94,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.22/0.81    inference(cnf_transformation,[],[f3])).
% 3.22/0.81  fof(f3,axiom,(
% 3.22/0.81    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.22/0.81  fof(f1932,plain,(
% 3.22/0.81    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)))) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_107 | ~spl2_135)),
% 3.22/0.81    inference(forward_demodulation,[],[f1931,f1725])).
% 3.22/0.81  fof(f1931,plain,(
% 3.22/0.81    ~r1_tarski(sK1,k2_xboole_0(sK1,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)))) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_107 | ~spl2_135)),
% 3.22/0.81    inference(forward_demodulation,[],[f1911,f1725])).
% 3.22/0.81  fof(f1911,plain,(
% 3.22/0.81    ~r1_tarski(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1))) | r1_tarski(sK1,k1_tops_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)))) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_107)),
% 3.22/0.81    inference(resolution,[],[f1907,f1378])).
% 3.22/0.81  fof(f1378,plain,(
% 3.22/0.81    m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_107),
% 3.22/0.81    inference(avatar_component_clause,[],[f1377])).
% 3.22/0.81  fof(f1907,plain,(
% 3.22/0.81    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 3.22/0.81    inference(subsumption_resolution,[],[f139,f149])).
% 3.22/0.81  fof(f149,plain,(
% 3.22/0.81    v3_pre_topc(sK1,sK0) | ~spl2_5),
% 3.22/0.81    inference(avatar_component_clause,[],[f148])).
% 3.22/0.81  fof(f139,plain,(
% 3.22/0.81    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_3)),
% 3.22/0.81    inference(subsumption_resolution,[],[f121,f109])).
% 3.22/0.81  fof(f109,plain,(
% 3.22/0.81    l1_pre_topc(sK0) | ~spl2_2),
% 3.22/0.81    inference(avatar_component_clause,[],[f108])).
% 3.22/0.81  fof(f121,plain,(
% 3.22/0.81    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f78])).
% 3.22/0.81  fof(f78,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f51])).
% 3.22/0.81  fof(f51,plain,(
% 3.22/0.81    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.81    inference(flattening,[],[f50])).
% 3.22/0.81  fof(f50,plain,(
% 3.22/0.81    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f32])).
% 3.22/0.81  fof(f32,axiom,(
% 3.22/0.81    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.22/0.81  fof(f113,plain,(
% 3.22/0.81    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.22/0.81    inference(avatar_component_clause,[],[f112])).
% 3.22/0.81  fof(f1904,plain,(
% 3.22/0.81    spl2_149 | ~spl2_6 | ~spl2_30),
% 3.22/0.81    inference(avatar_split_clause,[],[f1873,f414,f151,f1902])).
% 3.22/0.81  fof(f151,plain,(
% 3.22/0.81    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.22/0.81  fof(f414,plain,(
% 3.22/0.81    spl2_30 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 3.22/0.81  fof(f1873,plain,(
% 3.22/0.81    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_6 | ~spl2_30)),
% 3.22/0.81    inference(superposition,[],[f462,f152])).
% 3.22/0.81  fof(f152,plain,(
% 3.22/0.81    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_6),
% 3.22/0.81    inference(avatar_component_clause,[],[f151])).
% 3.22/0.81  fof(f462,plain,(
% 3.22/0.81    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)) ) | ~spl2_30),
% 3.22/0.81    inference(resolution,[],[f415,f70])).
% 3.22/0.81  fof(f70,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f40])).
% 3.22/0.81  fof(f40,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f22])).
% 3.22/0.81  fof(f22,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.22/0.81  fof(f415,plain,(
% 3.22/0.81    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_30),
% 3.22/0.81    inference(avatar_component_clause,[],[f414])).
% 3.22/0.81  fof(f1880,plain,(
% 3.22/0.81    spl2_147 | ~spl2_122 | ~spl2_125 | ~spl2_144),
% 3.22/0.81    inference(avatar_split_clause,[],[f1868,f1845,f1629,f1569,f1878])).
% 3.22/0.81  fof(f1868,plain,(
% 3.22/0.81    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) | (~spl2_122 | ~spl2_125 | ~spl2_144)),
% 3.22/0.81    inference(forward_demodulation,[],[f1860,f1866])).
% 3.22/0.81  fof(f1860,plain,(
% 3.22/0.81    m1_subset_1(k3_subset_1(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,sK1)),k1_zfmisc_1(k1_tops_1(sK0,sK1))) | ~spl2_144),
% 3.22/0.81    inference(resolution,[],[f1846,f88])).
% 3.22/0.81  fof(f88,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f56])).
% 3.22/0.81  fof(f56,plain,(
% 3.22/0.81    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f17])).
% 3.22/0.81  fof(f17,axiom,(
% 3.22/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.22/0.81  fof(f1847,plain,(
% 3.22/0.81    spl2_144 | ~spl2_141),
% 3.22/0.81    inference(avatar_split_clause,[],[f1824,f1813,f1845])).
% 3.22/0.81  fof(f1813,plain,(
% 3.22/0.81    spl2_141 <=> r1_tarski(k4_xboole_0(sK1,sK1),k1_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_141])])).
% 3.22/0.81  fof(f1824,plain,(
% 3.22/0.81    m1_subset_1(k4_xboole_0(sK1,sK1),k1_zfmisc_1(k1_tops_1(sK0,sK1))) | ~spl2_141),
% 3.22/0.81    inference(resolution,[],[f1814,f92])).
% 3.22/0.81  fof(f92,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f27])).
% 3.22/0.81  fof(f27,axiom,(
% 3.22/0.81    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.22/0.81  fof(f1814,plain,(
% 3.22/0.81    r1_tarski(k4_xboole_0(sK1,sK1),k1_tops_1(sK0,sK1)) | ~spl2_141),
% 3.22/0.81    inference(avatar_component_clause,[],[f1813])).
% 3.22/0.81  fof(f1815,plain,(
% 3.22/0.81    spl2_141 | ~spl2_122),
% 3.22/0.81    inference(avatar_split_clause,[],[f1709,f1569,f1813])).
% 3.22/0.81  fof(f1709,plain,(
% 3.22/0.81    r1_tarski(k4_xboole_0(sK1,sK1),k1_tops_1(sK0,sK1)) | ~spl2_122),
% 3.22/0.81    inference(superposition,[],[f84,f1570])).
% 3.22/0.81  fof(f84,plain,(
% 3.22/0.81    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f9])).
% 3.22/0.81  fof(f9,axiom,(
% 3.22/0.81    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.22/0.81  fof(f1726,plain,(
% 3.22/0.81    spl2_135 | ~spl2_44 | ~spl2_122),
% 3.22/0.81    inference(avatar_split_clause,[],[f1714,f1569,f616,f1724])).
% 3.22/0.81  fof(f1714,plain,(
% 3.22/0.81    sK1 = k2_xboole_0(sK1,sK1) | (~spl2_44 | ~spl2_122)),
% 3.22/0.81    inference(forward_demodulation,[],[f1713,f617])).
% 3.22/0.81  fof(f1713,plain,(
% 3.22/0.81    k2_xboole_0(sK1,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_122),
% 3.22/0.81    inference(forward_demodulation,[],[f1710,f82])).
% 3.22/0.81  fof(f82,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f10])).
% 3.22/0.81  fof(f10,axiom,(
% 3.22/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.22/0.81  fof(f1710,plain,(
% 3.22/0.81    k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK1)) | ~spl2_122),
% 3.22/0.81    inference(superposition,[],[f82,f1570])).
% 3.22/0.81  fof(f1631,plain,(
% 3.22/0.81    spl2_125 | ~spl2_96),
% 3.22/0.81    inference(avatar_split_clause,[],[f1365,f1250,f1629])).
% 3.22/0.81  fof(f1250,plain,(
% 3.22/0.81    spl2_96 <=> k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 3.22/0.81  fof(f1365,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_96),
% 3.22/0.81    inference(superposition,[],[f1251,f100])).
% 3.22/0.81  fof(f1251,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_96),
% 3.22/0.81    inference(avatar_component_clause,[],[f1250])).
% 3.22/0.81  fof(f1571,plain,(
% 3.22/0.81    spl2_122 | ~spl2_42),
% 3.22/0.81    inference(avatar_split_clause,[],[f614,f603,f1569])).
% 3.22/0.81  fof(f603,plain,(
% 3.22/0.81    spl2_42 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 3.22/0.81  fof(f614,plain,(
% 3.22/0.81    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_42),
% 3.22/0.81    inference(superposition,[],[f81,f604])).
% 3.22/0.81  fof(f604,plain,(
% 3.22/0.81    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_42),
% 3.22/0.81    inference(avatar_component_clause,[],[f603])).
% 3.22/0.81  fof(f81,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f11])).
% 3.22/0.81  fof(f11,axiom,(
% 3.22/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.22/0.81  fof(f1498,plain,(
% 3.22/0.81    spl2_114 | ~spl2_26 | ~spl2_36),
% 3.22/0.81    inference(avatar_split_clause,[],[f546,f524,f311,f1496])).
% 3.22/0.81  fof(f524,plain,(
% 3.22/0.81    spl2_36 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 3.22/0.81  fof(f546,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_26 | ~spl2_36)),
% 3.22/0.81    inference(forward_demodulation,[],[f545,f312])).
% 3.22/0.81  fof(f545,plain,(
% 3.22/0.81    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_36),
% 3.22/0.81    inference(superposition,[],[f81,f525])).
% 3.22/0.81  fof(f525,plain,(
% 3.22/0.81    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_36),
% 3.22/0.81    inference(avatar_component_clause,[],[f524])).
% 3.22/0.81  fof(f1489,plain,(
% 3.22/0.81    spl2_113 | ~spl2_3 | ~spl2_9 | ~spl2_22 | ~spl2_26),
% 3.22/0.81    inference(avatar_split_clause,[],[f509,f311,f293,f171,f112,f1487])).
% 3.22/0.81  fof(f171,plain,(
% 3.22/0.81    spl2_9 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.22/0.81  fof(f293,plain,(
% 3.22/0.81    spl2_22 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 3.22/0.81  fof(f509,plain,(
% 3.22/0.81    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_9 | ~spl2_22 | ~spl2_26)),
% 3.22/0.81    inference(forward_demodulation,[],[f508,f317])).
% 3.22/0.81  fof(f317,plain,(
% 3.22/0.81    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_9 | ~spl2_22)),
% 3.22/0.81    inference(forward_demodulation,[],[f315,f294])).
% 3.22/0.81  fof(f294,plain,(
% 3.22/0.81    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_22),
% 3.22/0.81    inference(avatar_component_clause,[],[f293])).
% 3.22/0.81  fof(f315,plain,(
% 3.22/0.81    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_9)),
% 3.22/0.81    inference(resolution,[],[f129,f172])).
% 3.22/0.81  fof(f172,plain,(
% 3.22/0.81    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 3.22/0.81    inference(avatar_component_clause,[],[f171])).
% 3.22/0.81  fof(f129,plain,(
% 3.22/0.81    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X5) = k4_subset_1(u1_struct_0(sK0),sK1,X5)) ) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f89])).
% 3.22/0.81  fof(f89,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f58])).
% 3.22/0.81  fof(f58,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(flattening,[],[f57])).
% 3.22/0.81  fof(f57,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.22/0.81    inference(ennf_transformation,[],[f21])).
% 3.22/0.81  fof(f21,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.22/0.81  fof(f508,plain,(
% 3.22/0.81    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_26),
% 3.22/0.81    inference(forward_demodulation,[],[f505,f99])).
% 3.22/0.81  fof(f99,plain,(
% 3.22/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f1])).
% 3.22/0.81  fof(f1,axiom,(
% 3.22/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.22/0.81  fof(f505,plain,(
% 3.22/0.81    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_26),
% 3.22/0.81    inference(superposition,[],[f82,f312])).
% 3.22/0.81  fof(f1379,plain,(
% 3.22/0.81    spl2_107 | ~spl2_3 | ~spl2_28 | ~spl2_106),
% 3.22/0.81    inference(avatar_split_clause,[],[f1375,f1372,f406,f112,f1377])).
% 3.22/0.81  fof(f406,plain,(
% 3.22/0.81    spl2_28 <=> m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 3.22/0.81  fof(f1372,plain,(
% 3.22/0.81    spl2_106 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_106])])).
% 3.22/0.81  fof(f1375,plain,(
% 3.22/0.81    m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_28 | ~spl2_106)),
% 3.22/0.81    inference(forward_demodulation,[],[f1373,f419])).
% 3.22/0.81  fof(f419,plain,(
% 3.22/0.81    k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK1)) | (~spl2_3 | ~spl2_28)),
% 3.22/0.81    inference(resolution,[],[f407,f129])).
% 3.22/0.81  fof(f407,plain,(
% 3.22/0.81    m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_28),
% 3.22/0.81    inference(avatar_component_clause,[],[f406])).
% 3.22/0.81  fof(f1373,plain,(
% 3.22/0.81    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_106),
% 3.22/0.81    inference(avatar_component_clause,[],[f1372])).
% 3.22/0.81  fof(f1374,plain,(
% 3.22/0.81    spl2_106 | ~spl2_3 | ~spl2_28),
% 3.22/0.81    inference(avatar_split_clause,[],[f418,f406,f112,f1372])).
% 3.22/0.81  fof(f418,plain,(
% 3.22/0.81    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_28)),
% 3.22/0.81    inference(resolution,[],[f407,f130])).
% 3.22/0.81  fof(f130,plain,(
% 3.22/0.81    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X6),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f90])).
% 3.22/0.81  fof(f90,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f60])).
% 3.22/0.81  fof(f60,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(flattening,[],[f59])).
% 3.22/0.81  fof(f59,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.22/0.81    inference(ennf_transformation,[],[f18])).
% 3.22/0.81  fof(f18,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.22/0.81  fof(f1252,plain,(
% 3.22/0.81    spl2_96 | ~spl2_34),
% 3.22/0.81    inference(avatar_split_clause,[],[f518,f511,f1250])).
% 3.22/0.81  fof(f511,plain,(
% 3.22/0.81    spl2_34 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 3.22/0.81  fof(f518,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_34),
% 3.22/0.81    inference(resolution,[],[f512,f98])).
% 3.22/0.81  fof(f98,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.22/0.81    inference(cnf_transformation,[],[f64])).
% 3.22/0.81  fof(f64,plain,(
% 3.22/0.81    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.22/0.81    inference(ennf_transformation,[],[f8])).
% 3.22/0.81  fof(f8,axiom,(
% 3.22/0.81    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.22/0.81  fof(f512,plain,(
% 3.22/0.81    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_34),
% 3.22/0.81    inference(avatar_component_clause,[],[f511])).
% 3.22/0.81  fof(f835,plain,(
% 3.22/0.81    spl2_60 | ~spl2_1 | ~spl2_2 | ~spl2_58),
% 3.22/0.81    inference(avatar_split_clause,[],[f815,f779,f108,f104,f833])).
% 3.22/0.81  fof(f833,plain,(
% 3.22/0.81    spl2_60 <=> v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 3.22/0.81  fof(f104,plain,(
% 3.22/0.81    spl2_1 <=> v2_pre_topc(sK0)),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.22/0.81  fof(f779,plain,(
% 3.22/0.81    spl2_58 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 3.22/0.81  fof(f815,plain,(
% 3.22/0.81    v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_58)),
% 3.22/0.81    inference(subsumption_resolution,[],[f814,f105])).
% 3.22/0.81  fof(f105,plain,(
% 3.22/0.81    v2_pre_topc(sK0) | ~spl2_1),
% 3.22/0.81    inference(avatar_component_clause,[],[f104])).
% 3.22/0.81  fof(f814,plain,(
% 3.22/0.81    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | (~spl2_2 | ~spl2_58)),
% 3.22/0.81    inference(subsumption_resolution,[],[f795,f109])).
% 3.22/0.81  fof(f795,plain,(
% 3.22/0.81    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | ~spl2_58),
% 3.22/0.81    inference(resolution,[],[f780,f77])).
% 3.22/0.81  fof(f77,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f49])).
% 3.22/0.81  fof(f49,plain,(
% 3.22/0.81    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.22/0.81    inference(flattening,[],[f48])).
% 3.22/0.81  fof(f48,plain,(
% 3.22/0.81    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f30])).
% 3.22/0.81  fof(f30,axiom,(
% 3.22/0.81    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.22/0.81  fof(f780,plain,(
% 3.22/0.81    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_58),
% 3.22/0.81    inference(avatar_component_clause,[],[f779])).
% 3.22/0.81  fof(f781,plain,(
% 3.22/0.81    spl2_58 | ~spl2_56),
% 3.22/0.81    inference(avatar_split_clause,[],[f772,f755,f779])).
% 3.22/0.81  fof(f755,plain,(
% 3.22/0.81    spl2_56 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 3.22/0.81  fof(f772,plain,(
% 3.22/0.81    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_56),
% 3.22/0.81    inference(resolution,[],[f756,f92])).
% 3.22/0.81  fof(f756,plain,(
% 3.22/0.81    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_56),
% 3.22/0.81    inference(avatar_component_clause,[],[f755])).
% 3.22/0.81  fof(f757,plain,(
% 3.22/0.81    spl2_56 | ~spl2_4 | ~spl2_34),
% 3.22/0.81    inference(avatar_split_clause,[],[f753,f511,f144,f755])).
% 3.22/0.81  fof(f144,plain,(
% 3.22/0.81    spl2_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.22/0.81  fof(f753,plain,(
% 3.22/0.81    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_4 | ~spl2_34)),
% 3.22/0.81    inference(resolution,[],[f522,f145])).
% 3.22/0.81  fof(f145,plain,(
% 3.22/0.81    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_4),
% 3.22/0.81    inference(avatar_component_clause,[],[f144])).
% 3.22/0.81  fof(f522,plain,(
% 3.22/0.81    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl2_34),
% 3.22/0.81    inference(resolution,[],[f512,f91])).
% 3.22/0.81  fof(f91,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f62])).
% 3.22/0.81  fof(f62,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.22/0.81    inference(flattening,[],[f61])).
% 3.22/0.81  fof(f61,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.22/0.81    inference(ennf_transformation,[],[f7])).
% 3.22/0.81  fof(f7,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.22/0.81  fof(f618,plain,(
% 3.22/0.81    spl2_44 | ~spl2_42),
% 3.22/0.81    inference(avatar_split_clause,[],[f610,f603,f616])).
% 3.22/0.81  fof(f610,plain,(
% 3.22/0.81    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_42),
% 3.22/0.81    inference(superposition,[],[f604,f99])).
% 3.22/0.81  fof(f605,plain,(
% 3.22/0.81    spl2_42 | ~spl2_34),
% 3.22/0.81    inference(avatar_split_clause,[],[f519,f511,f603])).
% 3.22/0.81  fof(f519,plain,(
% 3.22/0.81    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl2_34),
% 3.22/0.81    inference(resolution,[],[f512,f97])).
% 3.22/0.81  fof(f526,plain,(
% 3.22/0.81    spl2_36 | ~spl2_3 | ~spl2_9 | ~spl2_22),
% 3.22/0.81    inference(avatar_split_clause,[],[f317,f293,f171,f112,f524])).
% 3.22/0.81  fof(f513,plain,(
% 3.22/0.81    spl2_34 | ~spl2_26),
% 3.22/0.81    inference(avatar_split_clause,[],[f504,f311,f511])).
% 3.22/0.81  fof(f504,plain,(
% 3.22/0.81    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_26),
% 3.22/0.81    inference(superposition,[],[f84,f312])).
% 3.22/0.81  fof(f416,plain,(
% 3.22/0.81    spl2_30 | ~spl2_3 | ~spl2_9 | ~spl2_22),
% 3.22/0.81    inference(avatar_split_clause,[],[f354,f293,f171,f112,f414])).
% 3.22/0.81  fof(f354,plain,(
% 3.22/0.81    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_9 | ~spl2_22)),
% 3.22/0.81    inference(forward_demodulation,[],[f350,f294])).
% 3.22/0.81  fof(f350,plain,(
% 3.22/0.81    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_9)),
% 3.22/0.81    inference(resolution,[],[f130,f172])).
% 3.22/0.81  fof(f408,plain,(
% 3.22/0.81    spl2_28 | ~spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f353,f112,f406])).
% 3.22/0.81  fof(f353,plain,(
% 3.22/0.81    m1_subset_1(k2_xboole_0(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.22/0.81    inference(forward_demodulation,[],[f349,f314])).
% 3.22/0.81  fof(f314,plain,(
% 3.22/0.81    k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f129,f113])).
% 3.22/0.81  fof(f349,plain,(
% 3.22/0.81    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f130,f113])).
% 3.22/0.81  fof(f313,plain,(
% 3.22/0.81    spl2_26 | ~spl2_3 | ~spl2_19),
% 3.22/0.81    inference(avatar_split_clause,[],[f296,f282,f112,f311])).
% 3.22/0.81  fof(f282,plain,(
% 3.22/0.81    spl2_19 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 3.22/0.81  fof(f296,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_19)),
% 3.22/0.81    inference(superposition,[],[f283,f122])).
% 3.22/0.81  fof(f122,plain,(
% 3.22/0.81    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f70])).
% 3.22/0.81  fof(f283,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_19),
% 3.22/0.81    inference(avatar_component_clause,[],[f282])).
% 3.22/0.81  fof(f305,plain,(
% 3.22/0.81    spl2_24 | ~spl2_2 | ~spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f132,f112,f108,f303])).
% 3.22/0.81  fof(f303,plain,(
% 3.22/0.81    spl2_24 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.22/0.81    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 3.22/0.81  fof(f132,plain,(
% 3.22/0.81    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.22/0.81    inference(subsumption_resolution,[],[f115,f109])).
% 3.22/0.81  fof(f115,plain,(
% 3.22/0.81    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f72])).
% 3.22/0.81  fof(f72,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f42])).
% 3.22/0.81  fof(f42,plain,(
% 3.22/0.81    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f31])).
% 3.22/0.81  fof(f31,axiom,(
% 3.22/0.81    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.22/0.81  fof(f295,plain,(
% 3.22/0.81    spl2_22 | ~spl2_2 | ~spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f134,f112,f108,f293])).
% 3.22/0.81  fof(f134,plain,(
% 3.22/0.81    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.22/0.81    inference(subsumption_resolution,[],[f117,f109])).
% 3.22/0.81  fof(f117,plain,(
% 3.22/0.81    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f74])).
% 3.22/0.81  fof(f74,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f44])).
% 3.22/0.81  fof(f44,plain,(
% 3.22/0.81    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f34])).
% 3.22/0.81  fof(f34,axiom,(
% 3.22/0.81    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.22/0.81  fof(f284,plain,(
% 3.22/0.81    spl2_19 | ~spl2_2 | ~spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f133,f112,f108,f282])).
% 3.22/0.81  fof(f133,plain,(
% 3.22/0.81    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.22/0.81    inference(subsumption_resolution,[],[f116,f109])).
% 3.22/0.81  fof(f116,plain,(
% 3.22/0.81    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f73])).
% 3.22/0.81  fof(f73,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f43])).
% 3.22/0.81  fof(f43,plain,(
% 3.22/0.81    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.81    inference(ennf_transformation,[],[f35])).
% 3.22/0.81  fof(f35,axiom,(
% 3.22/0.81    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.22/0.81  fof(f263,plain,(
% 3.22/0.81    spl2_14 | ~spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f258,f112,f261])).
% 3.22/0.81  fof(f258,plain,(
% 3.22/0.81    sK1 = k3_xboole_0(sK1,sK1) | ~spl2_3),
% 3.22/0.81    inference(superposition,[],[f125,f126])).
% 3.22/0.81  fof(f126,plain,(
% 3.22/0.81    ( ! [X4] : (k9_subset_1(u1_struct_0(sK0),X4,X4) = X4) ) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f86])).
% 3.22/0.81  fof(f86,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 3.22/0.81    inference(cnf_transformation,[],[f54])).
% 3.22/0.81  fof(f54,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f19])).
% 3.22/0.81  fof(f19,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.22/0.81  fof(f125,plain,(
% 3.22/0.81    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),X3,sK1) = k3_xboole_0(X3,sK1)) ) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f85])).
% 3.22/0.81  fof(f85,plain,(
% 3.22/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f53])).
% 3.22/0.81  fof(f53,plain,(
% 3.22/0.81    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f23])).
% 3.22/0.81  fof(f23,axiom,(
% 3.22/0.81    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 3.22/0.81  fof(f173,plain,(
% 3.22/0.81    spl2_9 | ~spl2_2 | ~spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f135,f112,f108,f171])).
% 3.22/0.81  fof(f135,plain,(
% 3.22/0.81    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 3.22/0.81    inference(subsumption_resolution,[],[f118,f109])).
% 3.22/0.81  fof(f118,plain,(
% 3.22/0.81    ~l1_pre_topc(sK0) | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f75])).
% 3.22/0.81  fof(f75,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.22/0.81    inference(cnf_transformation,[],[f46])).
% 3.22/0.81  fof(f46,plain,(
% 3.22/0.81    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.22/0.81    inference(flattening,[],[f45])).
% 3.22/0.81  fof(f45,plain,(
% 3.22/0.81    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f29])).
% 3.22/0.81  fof(f29,axiom,(
% 3.22/0.81    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.22/0.81  fof(f156,plain,(
% 3.22/0.81    ~spl2_5 | ~spl2_6),
% 3.22/0.81    inference(avatar_split_clause,[],[f154,f151,f148])).
% 3.22/0.81  fof(f154,plain,(
% 3.22/0.81    ~v3_pre_topc(sK1,sK0) | ~spl2_6),
% 3.22/0.81    inference(subsumption_resolution,[],[f66,f152])).
% 3.22/0.81  fof(f66,plain,(
% 3.22/0.81    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.22/0.81    inference(cnf_transformation,[],[f39])).
% 3.22/0.81  fof(f39,plain,(
% 3.22/0.81    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.22/0.81    inference(flattening,[],[f38])).
% 3.22/0.81  fof(f38,plain,(
% 3.22/0.81    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.22/0.81    inference(ennf_transformation,[],[f37])).
% 3.22/0.81  fof(f37,negated_conjecture,(
% 3.22/0.81    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.22/0.81    inference(negated_conjecture,[],[f36])).
% 3.22/0.81  fof(f36,conjecture,(
% 3.22/0.81    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.22/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.22/0.81  fof(f153,plain,(
% 3.22/0.81    spl2_5 | spl2_6),
% 3.22/0.81    inference(avatar_split_clause,[],[f65,f151,f148])).
% 3.22/0.81  fof(f65,plain,(
% 3.22/0.81    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.22/0.81    inference(cnf_transformation,[],[f39])).
% 3.22/0.81  fof(f146,plain,(
% 3.22/0.81    spl2_4 | ~spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f131,f112,f144])).
% 3.22/0.81  fof(f131,plain,(
% 3.22/0.81    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 3.22/0.81    inference(resolution,[],[f113,f93])).
% 3.22/0.81  fof(f93,plain,(
% 3.22/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.22/0.81    inference(cnf_transformation,[],[f27])).
% 3.22/0.81  fof(f114,plain,(
% 3.22/0.81    spl2_3),
% 3.22/0.81    inference(avatar_split_clause,[],[f67,f112])).
% 3.22/0.81  fof(f67,plain,(
% 3.22/0.81    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.81    inference(cnf_transformation,[],[f39])).
% 3.22/0.81  fof(f110,plain,(
% 3.22/0.81    spl2_2),
% 3.22/0.81    inference(avatar_split_clause,[],[f69,f108])).
% 3.22/0.81  fof(f69,plain,(
% 3.22/0.81    l1_pre_topc(sK0)),
% 3.22/0.81    inference(cnf_transformation,[],[f39])).
% 3.22/0.81  fof(f106,plain,(
% 3.22/0.81    spl2_1),
% 3.22/0.81    inference(avatar_split_clause,[],[f68,f104])).
% 3.22/0.81  fof(f68,plain,(
% 3.22/0.81    v2_pre_topc(sK0)),
% 3.22/0.81    inference(cnf_transformation,[],[f39])).
% 3.22/0.81  % SZS output end Proof for theBenchmark
% 3.22/0.81  % (2815)------------------------------
% 3.22/0.81  % (2815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.81  % (2815)Termination reason: Refutation
% 3.22/0.81  
% 3.22/0.81  % (2815)Memory used [KB]: 8315
% 3.22/0.81  % (2815)Time elapsed: 0.400 s
% 3.22/0.81  % (2815)------------------------------
% 3.22/0.81  % (2815)------------------------------
% 3.22/0.81  % (2784)Success in time 0.453 s
%------------------------------------------------------------------------------
