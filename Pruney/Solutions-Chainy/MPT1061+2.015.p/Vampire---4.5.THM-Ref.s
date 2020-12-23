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
% DateTime   : Thu Dec  3 13:07:34 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  251 ( 532 expanded)
%              Number of leaves         :   63 ( 225 expanded)
%              Depth                    :   11
%              Number of atoms          :  715 (1541 expanded)
%              Number of equality atoms :  101 ( 220 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1836,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f141,f146,f328,f377,f441,f459,f471,f561,f677,f781,f816,f945,f1046,f1120,f1183,f1190,f1202,f1204,f1218,f1223,f1390,f1396,f1431,f1456,f1477,f1644,f1658,f1668,f1690,f1695,f1698,f1705,f1721,f1795,f1834,f1835])).

fof(f1835,plain,
    ( k2_relat_1(k1_xboole_0) != k9_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 != sK1
    | k1_xboole_0 != sK2
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k9_relat_1(sK4,k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1834,plain,
    ( spl5_178
    | ~ spl5_173 ),
    inference(avatar_split_clause,[],[f1813,f1792,f1831])).

fof(f1831,plain,
    ( spl5_178
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1792,plain,
    ( spl5_173
  <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f1813,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_173 ),
    inference(resolution,[],[f1794,f185])).

fof(f185,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1794,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_173 ),
    inference(avatar_component_clause,[],[f1792])).

fof(f1795,plain,
    ( spl5_173
    | ~ spl5_148
    | ~ spl5_163
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1790,f1718,f1665,f1474,f1792])).

fof(f1474,plain,
    ( spl5_148
  <=> k2_relat_1(k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f1665,plain,
    ( spl5_163
  <=> r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f1718,plain,
    ( spl5_167
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f1790,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_148
    | ~ spl5_163
    | ~ spl5_167 ),
    inference(forward_demodulation,[],[f1748,f1476])).

fof(f1476,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl5_148 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f1748,plain,
    ( r1_tarski(k9_relat_1(sK4,k1_xboole_0),k1_xboole_0)
    | ~ spl5_163
    | ~ spl5_167 ),
    inference(backward_demodulation,[],[f1667,f1720])).

fof(f1720,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_167 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f1667,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_163 ),
    inference(avatar_component_clause,[],[f1665])).

fof(f1721,plain,
    ( ~ spl5_107
    | spl5_167
    | ~ spl5_102
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f1716,f1247,f1043,f1718,f1073])).

fof(f1073,plain,
    ( spl5_107
  <=> v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f1043,plain,
    ( spl5_102
  <=> v1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f1247,plain,
    ( spl5_124
  <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f1716,plain,
    ( k1_xboole_0 = sK1
    | ~ v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_102
    | ~ spl5_124 ),
    inference(forward_demodulation,[],[f1128,f1248])).

fof(f1248,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f1247])).

fof(f1128,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_102 ),
    inference(resolution,[],[f1045,f209])).

fof(f209,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f185,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1045,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1705,plain,
    ( spl5_103
    | ~ spl5_100
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f1704,f1215,f1033,f1050])).

fof(f1050,plain,
    ( spl5_103
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f1033,plain,
    ( spl5_100
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f1215,plain,
    ( spl5_122
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f1704,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_100
    | ~ spl5_122 ),
    inference(forward_demodulation,[],[f1700,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1700,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl5_100
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f1034,f1217])).

fof(f1217,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f1215])).

fof(f1034,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_100 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f1698,plain,
    ( ~ spl5_103
    | spl5_107 ),
    inference(avatar_split_clause,[],[f1132,f1073,f1050])).

fof(f1132,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))
    | spl5_107 ),
    inference(forward_demodulation,[],[f1130,f93])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1130,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | spl5_107 ),
    inference(resolution,[],[f1075,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1075,plain,
    ( ~ v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)
    | spl5_107 ),
    inference(avatar_component_clause,[],[f1073])).

fof(f1695,plain,
    ( ~ spl5_142
    | spl5_166 ),
    inference(avatar_contradiction_clause,[],[f1692])).

fof(f1692,plain,
    ( $false
    | ~ spl5_142
    | spl5_166 ),
    inference(unit_resulting_resolution,[],[f1389,f1689])).

fof(f1689,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_166 ),
    inference(avatar_component_clause,[],[f1687])).

fof(f1687,plain,
    ( spl5_166
  <=> v1_funct_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f1389,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f1388])).

fof(f1388,plain,
    ( spl5_142
  <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1690,plain,
    ( ~ spl5_166
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f1685,f138,f125,f115,f1687])).

fof(f115,plain,
    ( spl5_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f125,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f138,plain,
    ( spl5_9
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1685,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9 ),
    inference(forward_demodulation,[],[f140,f1007])).

fof(f1007,plain,
    ( ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f645,f117])).

fof(f117,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f645,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2) )
    | ~ spl5_6 ),
    inference(resolution,[],[f87,f127])).

fof(f127,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f140,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1668,plain,
    ( spl5_163
    | ~ spl5_55
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f1659,f1215,f558,f1665])).

fof(f558,plain,
    ( spl5_55
  <=> r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f1659,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_55
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f560,f1217])).

fof(f560,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f558])).

fof(f1658,plain,
    ( spl5_121
    | ~ spl5_123
    | ~ spl5_124 ),
    inference(avatar_split_clause,[],[f1651,f1247,f1220,f1211])).

fof(f1211,plain,
    ( spl5_121
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f1220,plain,
    ( spl5_123
  <=> k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f1651,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_123
    | ~ spl5_124 ),
    inference(backward_demodulation,[],[f1222,f1248])).

fof(f1222,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f1644,plain,
    ( spl5_124
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f1641,f735,f367,f110,f1247])).

fof(f110,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f367,plain,
    ( spl5_30
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f735,plain,
    ( spl5_72
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f1641,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_3
    | ~ spl5_30
    | ~ spl5_72 ),
    inference(resolution,[],[f820,f112])).

fof(f112,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f820,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl5_30
    | ~ spl5_72 ),
    inference(backward_demodulation,[],[f379,f737])).

fof(f737,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f735])).

fof(f379,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK4))
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl5_30 ),
    inference(resolution,[],[f368,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f368,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f367])).

fof(f1477,plain,
    ( spl5_148
    | ~ spl5_30
    | ~ spl5_147 ),
    inference(avatar_split_clause,[],[f1469,f1453,f367,f1474])).

fof(f1453,plain,
    ( spl5_147
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).

fof(f1469,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)
    | ~ spl5_30
    | ~ spl5_147 ),
    inference(superposition,[],[f380,f1455])).

fof(f1455,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl5_147 ),
    inference(avatar_component_clause,[],[f1453])).

fof(f380,plain,
    ( ! [X2] : k2_relat_1(k7_relat_1(sK4,X2)) = k9_relat_1(sK4,X2)
    | ~ spl5_30 ),
    inference(resolution,[],[f368,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1456,plain,
    ( spl5_147
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1442,f456,f1453])).

fof(f456,plain,
    ( spl5_42
  <=> r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1442,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl5_42 ),
    inference(resolution,[],[f458,f185])).

fof(f458,plain,
    ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f456])).

fof(f1431,plain,
    ( ~ spl5_30
    | spl5_51
    | spl5_41 ),
    inference(avatar_split_clause,[],[f1428,f452,f509,f367])).

fof(f509,plain,
    ( spl5_51
  <=> ! [X0] : ~ v4_relat_1(sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f452,plain,
    ( spl5_41
  <=> v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1428,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4) )
    | spl5_41 ),
    inference(resolution,[],[f454,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f454,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | spl5_41 ),
    inference(avatar_component_clause,[],[f452])).

fof(f1396,plain,
    ( spl5_40
    | ~ spl5_142 ),
    inference(avatar_contradiction_clause,[],[f1394])).

fof(f1394,plain,
    ( $false
    | spl5_40
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f450,f1389])).

fof(f450,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,k1_xboole_0))
    | spl5_40 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl5_40
  <=> v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f1390,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_142
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f1382,f125,f115,f1388,f115,f125])).

fof(f1382,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(sK4,X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ v1_funct_1(sK4) )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(superposition,[],[f88,f1007])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f1223,plain,
    ( spl5_123
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f1208,f1033,f1220])).

fof(f1208,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_100 ),
    inference(resolution,[],[f1034,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1218,plain,
    ( spl5_120
    | ~ spl5_121
    | spl5_122
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f1206,f1033,f1215,f1211,f1199])).

fof(f1199,plain,
    ( spl5_120
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f1206,plain,
    ( k1_xboole_0 = sK2
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_100 ),
    inference(resolution,[],[f1034,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f1204,plain,
    ( spl5_100
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f1203,f130,f125,f115,f1033])).

fof(f130,plain,
    ( spl5_7
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1203,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f131,f1007])).

fof(f131,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1202,plain,
    ( ~ spl5_120
    | ~ spl5_4
    | ~ spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f1197,f134,f125,f115,f1199])).

fof(f134,plain,
    ( spl5_8
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1197,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_8 ),
    inference(forward_demodulation,[],[f136,f1007])).

fof(f136,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1190,plain,
    ( ~ spl5_30
    | spl5_51
    | spl5_118 ),
    inference(avatar_split_clause,[],[f1185,f1180,f509,f367])).

fof(f1180,plain,
    ( spl5_118
  <=> v4_relat_1(k7_relat_1(sK4,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f1185,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK4,X0)
        | ~ v1_relat_1(sK4) )
    | spl5_118 ),
    inference(resolution,[],[f1182,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1182,plain,
    ( ~ v4_relat_1(k7_relat_1(sK4,sK1),sK1)
    | spl5_118 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1183,plain,
    ( ~ spl5_118
    | ~ spl5_102
    | spl5_115 ),
    inference(avatar_split_clause,[],[f1178,f1117,f1043,f1180])).

fof(f1117,plain,
    ( spl5_115
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f1178,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ v4_relat_1(k7_relat_1(sK4,sK1),sK1)
    | spl5_115 ),
    inference(resolution,[],[f1119,f65])).

fof(f1119,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl5_115 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1120,plain,
    ( ~ spl5_115
    | ~ spl5_55
    | ~ spl5_102
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f1115,f367,f130,f125,f115,f1043,f558,f1117])).

fof(f1115,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f1114,f1007])).

fof(f1114,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f1113,f380])).

fof(f1113,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f1112,f1007])).

fof(f1112,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f717,f1007])).

fof(f717,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_7 ),
    inference(resolution,[],[f132,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f132,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1046,plain,
    ( spl5_102
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f1015,f599,f125,f115,f1043])).

fof(f599,plain,
    ( spl5_56
  <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1015,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_56 ),
    inference(backward_demodulation,[],[f600,f1007])).

fof(f600,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f599])).

fof(f945,plain,
    ( k1_xboole_0 != sK3
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f816,plain,
    ( ~ spl5_5
    | spl5_77
    | spl5_72
    | ~ spl5_4
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f811,f325,f115,f735,f813,f120])).

fof(f120,plain,
    ( spl5_5
  <=> v1_funct_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f813,plain,
    ( spl5_77
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f325,plain,
    ( spl5_29
  <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f811,plain,
    ( sK0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f807,f327])).

fof(f327,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f325])).

fof(f807,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f82,f117])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f781,plain,
    ( ~ spl5_4
    | ~ spl5_51 ),
    inference(avatar_contradiction_clause,[],[f780])).

fof(f780,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f117,f776])).

fof(f776,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl5_51 ),
    inference(resolution,[],[f510,f76])).

fof(f510,plain,
    ( ! [X0] : ~ v4_relat_1(sK4,X0)
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f509])).

fof(f677,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_56 ),
    inference(avatar_split_clause,[],[f670,f599,f115,f125])).

fof(f670,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_56 ),
    inference(resolution,[],[f89,f614])).

fof(f614,plain,
    ( ! [X2,X3] : ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | spl5_56 ),
    inference(resolution,[],[f611,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f611,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0)) )
    | spl5_56 ),
    inference(resolution,[],[f601,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f601,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_56 ),
    inference(avatar_component_clause,[],[f599])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f561,plain,
    ( spl5_55
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f556,f115,f105,f558])).

fof(f105,plain,
    ( spl5_2
  <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f556,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f107,f550])).

fof(f550,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k7_relset_1(sK0,sK3,sK4,X0)
    | ~ spl5_4 ),
    inference(resolution,[],[f86,f117])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f107,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f471,plain,
    ( ~ spl5_41
    | ~ spl5_40
    | spl5_44
    | ~ spl5_30
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f466,f438,f367,f468,f448,f452])).

fof(f468,plain,
    ( spl5_44
  <=> v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k9_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f438,plain,
    ( spl5_39
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f466,plain,
    ( v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k9_relat_1(sK4,k1_xboole_0))
    | ~ v1_funct_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ spl5_30
    | ~ spl5_39 ),
    inference(forward_demodulation,[],[f444,f380])).

fof(f444,plain,
    ( v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k2_relat_1(k7_relat_1(sK4,k1_xboole_0)))
    | ~ v1_funct_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ spl5_39 ),
    inference(superposition,[],[f59,f440])).

fof(f440,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f438])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f459,plain,
    ( ~ spl5_40
    | ~ spl5_41
    | spl5_42
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f446,f438,f456,f452,f448])).

fof(f446,plain,
    ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ v1_funct_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ spl5_39 ),
    inference(forward_demodulation,[],[f442,f93])).

fof(f442,plain,
    ( r1_tarski(k7_relat_1(sK4,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK4,k1_xboole_0))))
    | ~ v1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ v1_funct_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ spl5_39 ),
    inference(superposition,[],[f257,f440])).

fof(f257,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f60,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f441,plain,
    ( spl5_39
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f430,f367,f438])).

fof(f430,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ spl5_30 ),
    inference(resolution,[],[f379,f56])).

fof(f377,plain,
    ( ~ spl5_4
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl5_4
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f61,f117,f369,f58])).

fof(f369,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f367])).

fof(f328,plain,
    ( spl5_29
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f318,f115,f325])).

fof(f318,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(resolution,[],[f75,f117])).

fof(f146,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f143,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f141,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f48,f138,f134,f130])).

fof(f48,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f128,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f49,f125])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f123,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f50,f120])).

fof(f50,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f118,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f51,f115])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f52,f110])).

fof(f52,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f108,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f100,plain,
    ( spl5_1
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f54,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (3296)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.47  % (3298)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (3314)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (3301)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.48  % (3310)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.48  % (3293)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (3300)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (3297)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (3313)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (3311)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (3292)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (3315)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (3305)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (3307)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (3294)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (3308)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (3295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (3303)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (3302)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (3306)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (3309)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (3316)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (3317)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (3299)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (3312)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  % (3304)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.77/0.59  % (3307)Refutation found. Thanks to Tanya!
% 1.77/0.59  % SZS status Theorem for theBenchmark
% 1.77/0.59  % SZS output start Proof for theBenchmark
% 1.77/0.59  fof(f1836,plain,(
% 1.77/0.59    $false),
% 1.77/0.59    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f141,f146,f328,f377,f441,f459,f471,f561,f677,f781,f816,f945,f1046,f1120,f1183,f1190,f1202,f1204,f1218,f1223,f1390,f1396,f1431,f1456,f1477,f1644,f1658,f1668,f1690,f1695,f1698,f1705,f1721,f1795,f1834,f1835])).
% 1.77/0.59  fof(f1835,plain,(
% 1.77/0.59    k2_relat_1(k1_xboole_0) != k9_relat_1(sK4,k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | k1_xboole_0 != sK1 | k1_xboole_0 != sK2 | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k9_relat_1(sK4,k1_xboole_0))),
% 1.77/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.77/0.59  fof(f1834,plain,(
% 1.77/0.59    spl5_178 | ~spl5_173),
% 1.77/0.59    inference(avatar_split_clause,[],[f1813,f1792,f1831])).
% 1.77/0.59  fof(f1831,plain,(
% 1.77/0.59    spl5_178 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).
% 1.77/0.59  fof(f1792,plain,(
% 1.77/0.59    spl5_173 <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).
% 1.77/0.59  fof(f1813,plain,(
% 1.77/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_173),
% 1.77/0.59    inference(resolution,[],[f1794,f185])).
% 1.77/0.59  fof(f185,plain,(
% 1.77/0.59    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.77/0.59    inference(resolution,[],[f68,f56])).
% 1.77/0.59  fof(f56,plain,(
% 1.77/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f3])).
% 1.77/0.59  fof(f3,axiom,(
% 1.77/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.77/0.59  fof(f68,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.77/0.59    inference(cnf_transformation,[],[f2])).
% 1.77/0.59  fof(f2,axiom,(
% 1.77/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.77/0.59  fof(f1794,plain,(
% 1.77/0.59    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | ~spl5_173),
% 1.77/0.59    inference(avatar_component_clause,[],[f1792])).
% 1.77/0.59  fof(f1795,plain,(
% 1.77/0.59    spl5_173 | ~spl5_148 | ~spl5_163 | ~spl5_167),
% 1.77/0.59    inference(avatar_split_clause,[],[f1790,f1718,f1665,f1474,f1792])).
% 1.77/0.59  fof(f1474,plain,(
% 1.77/0.59    spl5_148 <=> k2_relat_1(k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).
% 1.77/0.59  fof(f1665,plain,(
% 1.77/0.59    spl5_163 <=> r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).
% 1.77/0.59  fof(f1718,plain,(
% 1.77/0.59    spl5_167 <=> k1_xboole_0 = sK1),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).
% 1.77/0.59  fof(f1790,plain,(
% 1.77/0.59    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl5_148 | ~spl5_163 | ~spl5_167)),
% 1.77/0.59    inference(forward_demodulation,[],[f1748,f1476])).
% 1.77/0.59  fof(f1476,plain,(
% 1.77/0.59    k2_relat_1(k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) | ~spl5_148),
% 1.77/0.59    inference(avatar_component_clause,[],[f1474])).
% 1.77/0.59  fof(f1748,plain,(
% 1.77/0.59    r1_tarski(k9_relat_1(sK4,k1_xboole_0),k1_xboole_0) | (~spl5_163 | ~spl5_167)),
% 1.77/0.59    inference(backward_demodulation,[],[f1667,f1720])).
% 1.77/0.59  fof(f1720,plain,(
% 1.77/0.59    k1_xboole_0 = sK1 | ~spl5_167),
% 1.77/0.59    inference(avatar_component_clause,[],[f1718])).
% 1.77/0.59  fof(f1667,plain,(
% 1.77/0.59    r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) | ~spl5_163),
% 1.77/0.59    inference(avatar_component_clause,[],[f1665])).
% 1.77/0.59  fof(f1721,plain,(
% 1.77/0.59    ~spl5_107 | spl5_167 | ~spl5_102 | ~spl5_124),
% 1.77/0.59    inference(avatar_split_clause,[],[f1716,f1247,f1043,f1718,f1073])).
% 1.77/0.59  fof(f1073,plain,(
% 1.77/0.59    spl5_107 <=> v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 1.77/0.59  fof(f1043,plain,(
% 1.77/0.59    spl5_102 <=> v1_relat_1(k7_relat_1(sK4,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 1.77/0.59  fof(f1247,plain,(
% 1.77/0.59    spl5_124 <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 1.77/0.59  fof(f1716,plain,(
% 1.77/0.59    k1_xboole_0 = sK1 | ~v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_102 | ~spl5_124)),
% 1.77/0.59    inference(forward_demodulation,[],[f1128,f1248])).
% 1.77/0.59  fof(f1248,plain,(
% 1.77/0.59    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_124),
% 1.77/0.59    inference(avatar_component_clause,[],[f1247])).
% 1.77/0.59  fof(f1128,plain,(
% 1.77/0.59    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) | ~spl5_102),
% 1.77/0.59    inference(resolution,[],[f1045,f209])).
% 1.77/0.59  fof(f209,plain,(
% 1.77/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0)) )),
% 1.77/0.59    inference(resolution,[],[f185,f65])).
% 1.77/0.59  fof(f65,plain,(
% 1.77/0.59    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f34])).
% 1.77/0.59  fof(f34,plain,(
% 1.77/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.77/0.59    inference(ennf_transformation,[],[f9])).
% 1.77/0.59  fof(f9,axiom,(
% 1.77/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.77/0.59  fof(f1045,plain,(
% 1.77/0.59    v1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_102),
% 1.77/0.59    inference(avatar_component_clause,[],[f1043])).
% 1.77/0.59  fof(f1705,plain,(
% 1.77/0.59    spl5_103 | ~spl5_100 | ~spl5_122),
% 1.77/0.59    inference(avatar_split_clause,[],[f1704,f1215,f1033,f1050])).
% 1.77/0.59  fof(f1050,plain,(
% 1.77/0.59    spl5_103 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).
% 1.77/0.59  fof(f1033,plain,(
% 1.77/0.59    spl5_100 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 1.77/0.59  fof(f1215,plain,(
% 1.77/0.59    spl5_122 <=> k1_xboole_0 = sK2),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).
% 1.77/0.59  fof(f1704,plain,(
% 1.77/0.59    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl5_100 | ~spl5_122)),
% 1.77/0.59    inference(forward_demodulation,[],[f1700,f92])).
% 1.77/0.59  fof(f92,plain,(
% 1.77/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.77/0.59    inference(equality_resolution,[],[f73])).
% 1.77/0.59  fof(f73,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f4])).
% 1.77/0.59  fof(f4,axiom,(
% 1.77/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.77/0.59  fof(f1700,plain,(
% 1.77/0.59    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl5_100 | ~spl5_122)),
% 1.77/0.59    inference(backward_demodulation,[],[f1034,f1217])).
% 1.77/0.59  fof(f1217,plain,(
% 1.77/0.59    k1_xboole_0 = sK2 | ~spl5_122),
% 1.77/0.59    inference(avatar_component_clause,[],[f1215])).
% 1.77/0.59  fof(f1034,plain,(
% 1.77/0.59    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_100),
% 1.77/0.59    inference(avatar_component_clause,[],[f1033])).
% 1.77/0.59  fof(f1698,plain,(
% 1.77/0.59    ~spl5_103 | spl5_107),
% 1.77/0.59    inference(avatar_split_clause,[],[f1132,f1073,f1050])).
% 1.77/0.59  fof(f1132,plain,(
% 1.77/0.59    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) | spl5_107),
% 1.77/0.59    inference(forward_demodulation,[],[f1130,f93])).
% 1.77/0.59  fof(f93,plain,(
% 1.77/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.77/0.59    inference(equality_resolution,[],[f72])).
% 1.77/0.59  fof(f72,plain,(
% 1.77/0.59    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f4])).
% 1.77/0.59  fof(f1130,plain,(
% 1.77/0.59    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | spl5_107),
% 1.77/0.59    inference(resolution,[],[f1075,f76])).
% 1.77/0.59  fof(f76,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f38])).
% 1.77/0.59  fof(f38,plain,(
% 1.77/0.59    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.59    inference(ennf_transformation,[],[f24])).
% 1.77/0.59  fof(f24,plain,(
% 1.77/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.77/0.59    inference(pure_predicate_removal,[],[f14])).
% 1.77/0.59  fof(f14,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.77/0.59  fof(f1075,plain,(
% 1.77/0.59    ~v4_relat_1(k7_relat_1(sK4,sK1),k1_xboole_0) | spl5_107),
% 1.77/0.59    inference(avatar_component_clause,[],[f1073])).
% 1.77/0.59  fof(f1695,plain,(
% 1.77/0.59    ~spl5_142 | spl5_166),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f1692])).
% 1.77/0.59  fof(f1692,plain,(
% 1.77/0.59    $false | (~spl5_142 | spl5_166)),
% 1.77/0.59    inference(unit_resulting_resolution,[],[f1389,f1689])).
% 1.77/0.59  fof(f1689,plain,(
% 1.77/0.59    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl5_166),
% 1.77/0.59    inference(avatar_component_clause,[],[f1687])).
% 1.77/0.59  fof(f1687,plain,(
% 1.77/0.59    spl5_166 <=> v1_funct_1(k7_relat_1(sK4,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).
% 1.77/0.59  fof(f1389,plain,(
% 1.77/0.59    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1))) ) | ~spl5_142),
% 1.77/0.59    inference(avatar_component_clause,[],[f1388])).
% 1.77/0.59  fof(f1388,plain,(
% 1.77/0.59    spl5_142 <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).
% 1.77/0.59  fof(f1690,plain,(
% 1.77/0.59    ~spl5_166 | ~spl5_4 | ~spl5_6 | spl5_9),
% 1.77/0.59    inference(avatar_split_clause,[],[f1685,f138,f125,f115,f1687])).
% 1.77/0.59  fof(f115,plain,(
% 1.77/0.59    spl5_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.77/0.59  fof(f125,plain,(
% 1.77/0.59    spl5_6 <=> v1_funct_1(sK4)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.77/0.59  fof(f138,plain,(
% 1.77/0.59    spl5_9 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.77/0.59  fof(f1685,plain,(
% 1.77/0.59    ~v1_funct_1(k7_relat_1(sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_9)),
% 1.77/0.59    inference(forward_demodulation,[],[f140,f1007])).
% 1.77/0.59  fof(f1007,plain,(
% 1.77/0.59    ( ! [X0] : (k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl5_4 | ~spl5_6)),
% 1.77/0.59    inference(resolution,[],[f645,f117])).
% 1.77/0.59  fof(f117,plain,(
% 1.77/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_4),
% 1.77/0.59    inference(avatar_component_clause,[],[f115])).
% 1.77/0.59  fof(f645,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relat_1(sK4,X2) = k2_partfun1(X0,X1,sK4,X2)) ) | ~spl5_6),
% 1.77/0.59    inference(resolution,[],[f87,f127])).
% 1.77/0.59  fof(f127,plain,(
% 1.77/0.59    v1_funct_1(sK4) | ~spl5_6),
% 1.77/0.59    inference(avatar_component_clause,[],[f125])).
% 1.77/0.59  fof(f87,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f45])).
% 1.77/0.59  fof(f45,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.77/0.59    inference(flattening,[],[f44])).
% 1.77/0.59  fof(f44,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.77/0.59    inference(ennf_transformation,[],[f20])).
% 1.77/0.59  fof(f20,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.77/0.59  fof(f140,plain,(
% 1.77/0.59    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_9),
% 1.77/0.59    inference(avatar_component_clause,[],[f138])).
% 1.77/0.59  fof(f1668,plain,(
% 1.77/0.59    spl5_163 | ~spl5_55 | ~spl5_122),
% 1.77/0.59    inference(avatar_split_clause,[],[f1659,f1215,f558,f1665])).
% 1.77/0.59  fof(f558,plain,(
% 1.77/0.59    spl5_55 <=> r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.77/0.59  fof(f1659,plain,(
% 1.77/0.59    r1_tarski(k9_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_55 | ~spl5_122)),
% 1.77/0.59    inference(backward_demodulation,[],[f560,f1217])).
% 1.77/0.59  fof(f560,plain,(
% 1.77/0.59    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~spl5_55),
% 1.77/0.59    inference(avatar_component_clause,[],[f558])).
% 1.77/0.59  fof(f1658,plain,(
% 1.77/0.59    spl5_121 | ~spl5_123 | ~spl5_124),
% 1.77/0.59    inference(avatar_split_clause,[],[f1651,f1247,f1220,f1211])).
% 1.77/0.59  fof(f1211,plain,(
% 1.77/0.59    spl5_121 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).
% 1.77/0.59  fof(f1220,plain,(
% 1.77/0.59    spl5_123 <=> k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).
% 1.77/0.59  fof(f1651,plain,(
% 1.77/0.59    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl5_123 | ~spl5_124)),
% 1.77/0.59    inference(backward_demodulation,[],[f1222,f1248])).
% 1.77/0.59  fof(f1222,plain,(
% 1.77/0.59    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_123),
% 1.77/0.59    inference(avatar_component_clause,[],[f1220])).
% 1.77/0.59  fof(f1644,plain,(
% 1.77/0.59    spl5_124 | ~spl5_3 | ~spl5_30 | ~spl5_72),
% 1.77/0.59    inference(avatar_split_clause,[],[f1641,f735,f367,f110,f1247])).
% 1.77/0.59  fof(f110,plain,(
% 1.77/0.59    spl5_3 <=> r1_tarski(sK1,sK0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.77/0.59  fof(f367,plain,(
% 1.77/0.59    spl5_30 <=> v1_relat_1(sK4)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.77/0.59  fof(f735,plain,(
% 1.77/0.59    spl5_72 <=> sK0 = k1_relat_1(sK4)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 1.77/0.59  fof(f1641,plain,(
% 1.77/0.59    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_3 | ~spl5_30 | ~spl5_72)),
% 1.77/0.59    inference(resolution,[],[f820,f112])).
% 1.77/0.59  fof(f112,plain,(
% 1.77/0.59    r1_tarski(sK1,sK0) | ~spl5_3),
% 1.77/0.59    inference(avatar_component_clause,[],[f110])).
% 1.77/0.59  fof(f820,plain,(
% 1.77/0.59    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | (~spl5_30 | ~spl5_72)),
% 1.77/0.59    inference(backward_demodulation,[],[f379,f737])).
% 1.77/0.59  fof(f737,plain,(
% 1.77/0.59    sK0 = k1_relat_1(sK4) | ~spl5_72),
% 1.77/0.59    inference(avatar_component_clause,[],[f735])).
% 1.77/0.59  fof(f379,plain,(
% 1.77/0.59    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK4)) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | ~spl5_30),
% 1.77/0.59    inference(resolution,[],[f368,f63])).
% 1.77/0.59  fof(f63,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.77/0.59    inference(cnf_transformation,[],[f33])).
% 1.77/0.59  fof(f33,plain,(
% 1.77/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.77/0.59    inference(flattening,[],[f32])).
% 1.77/0.59  fof(f32,plain,(
% 1.77/0.59    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.77/0.59    inference(ennf_transformation,[],[f13])).
% 1.77/0.59  fof(f13,axiom,(
% 1.77/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.77/0.59  fof(f368,plain,(
% 1.77/0.59    v1_relat_1(sK4) | ~spl5_30),
% 1.77/0.59    inference(avatar_component_clause,[],[f367])).
% 1.77/0.59  fof(f1477,plain,(
% 1.77/0.59    spl5_148 | ~spl5_30 | ~spl5_147),
% 1.77/0.59    inference(avatar_split_clause,[],[f1469,f1453,f367,f1474])).
% 1.77/0.59  fof(f1453,plain,(
% 1.77/0.59    spl5_147 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_147])])).
% 1.77/0.59  fof(f1469,plain,(
% 1.77/0.59    k2_relat_1(k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) | (~spl5_30 | ~spl5_147)),
% 1.77/0.59    inference(superposition,[],[f380,f1455])).
% 1.77/0.59  fof(f1455,plain,(
% 1.77/0.59    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl5_147),
% 1.77/0.59    inference(avatar_component_clause,[],[f1453])).
% 1.77/0.59  fof(f380,plain,(
% 1.77/0.59    ( ! [X2] : (k2_relat_1(k7_relat_1(sK4,X2)) = k9_relat_1(sK4,X2)) ) | ~spl5_30),
% 1.77/0.59    inference(resolution,[],[f368,f62])).
% 1.77/0.59  fof(f62,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f31])).
% 1.77/0.59  fof(f31,plain,(
% 1.77/0.59    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.77/0.59    inference(ennf_transformation,[],[f12])).
% 1.77/0.59  fof(f12,axiom,(
% 1.77/0.59    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.77/0.59  fof(f1456,plain,(
% 1.77/0.59    spl5_147 | ~spl5_42),
% 1.77/0.59    inference(avatar_split_clause,[],[f1442,f456,f1453])).
% 1.77/0.59  fof(f456,plain,(
% 1.77/0.59    spl5_42 <=> r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.77/0.59  fof(f1442,plain,(
% 1.77/0.59    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl5_42),
% 1.77/0.59    inference(resolution,[],[f458,f185])).
% 1.77/0.59  fof(f458,plain,(
% 1.77/0.59    r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) | ~spl5_42),
% 1.77/0.59    inference(avatar_component_clause,[],[f456])).
% 1.77/0.59  fof(f1431,plain,(
% 1.77/0.59    ~spl5_30 | spl5_51 | spl5_41),
% 1.77/0.59    inference(avatar_split_clause,[],[f1428,f452,f509,f367])).
% 1.77/0.59  fof(f509,plain,(
% 1.77/0.59    spl5_51 <=> ! [X0] : ~v4_relat_1(sK4,X0)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 1.77/0.59  fof(f452,plain,(
% 1.77/0.59    spl5_41 <=> v1_relat_1(k7_relat_1(sK4,k1_xboole_0))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.77/0.59  fof(f1428,plain,(
% 1.77/0.59    ( ! [X0] : (~v4_relat_1(sK4,X0) | ~v1_relat_1(sK4)) ) | spl5_41),
% 1.77/0.59    inference(resolution,[],[f454,f83])).
% 1.77/0.59  fof(f83,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f42])).
% 1.77/0.59  fof(f42,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 1.77/0.59    inference(flattening,[],[f41])).
% 1.77/0.59  fof(f41,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 1.77/0.59    inference(ennf_transformation,[],[f10])).
% 1.77/0.59  fof(f10,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).
% 1.77/0.59  fof(f454,plain,(
% 1.77/0.59    ~v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | spl5_41),
% 1.77/0.59    inference(avatar_component_clause,[],[f452])).
% 1.77/0.59  fof(f1396,plain,(
% 1.77/0.59    spl5_40 | ~spl5_142),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f1394])).
% 1.77/0.59  fof(f1394,plain,(
% 1.77/0.59    $false | (spl5_40 | ~spl5_142)),
% 1.77/0.59    inference(subsumption_resolution,[],[f450,f1389])).
% 1.77/0.59  fof(f450,plain,(
% 1.77/0.59    ~v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) | spl5_40),
% 1.77/0.59    inference(avatar_component_clause,[],[f448])).
% 1.77/0.59  fof(f448,plain,(
% 1.77/0.59    spl5_40 <=> v1_funct_1(k7_relat_1(sK4,k1_xboole_0))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.77/0.59  fof(f1390,plain,(
% 1.77/0.59    ~spl5_6 | ~spl5_4 | spl5_142 | ~spl5_4 | ~spl5_6),
% 1.77/0.59    inference(avatar_split_clause,[],[f1382,f125,f115,f1388,f115,f125])).
% 1.77/0.59  fof(f1382,plain,(
% 1.77/0.59    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) ) | (~spl5_4 | ~spl5_6)),
% 1.77/0.59    inference(superposition,[],[f88,f1007])).
% 1.77/0.59  fof(f88,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f47])).
% 1.77/0.59  fof(f47,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.77/0.59    inference(flattening,[],[f46])).
% 1.77/0.59  fof(f46,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.77/0.59    inference(ennf_transformation,[],[f19])).
% 1.77/0.59  fof(f19,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.77/0.59  fof(f1223,plain,(
% 1.77/0.59    spl5_123 | ~spl5_100),
% 1.77/0.59    inference(avatar_split_clause,[],[f1208,f1033,f1220])).
% 1.77/0.59  fof(f1208,plain,(
% 1.77/0.59    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_100),
% 1.77/0.59    inference(resolution,[],[f1034,f75])).
% 1.77/0.59  fof(f75,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f37])).
% 1.77/0.59  fof(f37,plain,(
% 1.77/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.59    inference(ennf_transformation,[],[f15])).
% 1.77/0.59  fof(f15,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.77/0.59  fof(f1218,plain,(
% 1.77/0.59    spl5_120 | ~spl5_121 | spl5_122 | ~spl5_100),
% 1.77/0.59    inference(avatar_split_clause,[],[f1206,f1033,f1215,f1211,f1199])).
% 1.77/0.59  fof(f1199,plain,(
% 1.77/0.59    spl5_120 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).
% 1.77/0.59  fof(f1206,plain,(
% 1.77/0.59    k1_xboole_0 = sK2 | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~spl5_100),
% 1.77/0.59    inference(resolution,[],[f1034,f81])).
% 1.77/0.59  fof(f81,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f40])).
% 1.77/0.59  fof(f40,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.59    inference(flattening,[],[f39])).
% 1.77/0.59  fof(f39,plain,(
% 1.77/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.59    inference(ennf_transformation,[],[f18])).
% 1.77/0.59  fof(f18,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.77/0.59  fof(f1204,plain,(
% 1.77/0.59    spl5_100 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 1.77/0.59    inference(avatar_split_clause,[],[f1203,f130,f125,f115,f1033])).
% 1.77/0.59  fof(f130,plain,(
% 1.77/0.59    spl5_7 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.77/0.59  fof(f1203,plain,(
% 1.77/0.59    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 1.77/0.59    inference(forward_demodulation,[],[f131,f1007])).
% 1.77/0.59  fof(f131,plain,(
% 1.77/0.59    m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_7),
% 1.77/0.59    inference(avatar_component_clause,[],[f130])).
% 1.77/0.59  fof(f1202,plain,(
% 1.77/0.59    ~spl5_120 | ~spl5_4 | ~spl5_6 | spl5_8),
% 1.77/0.59    inference(avatar_split_clause,[],[f1197,f134,f125,f115,f1199])).
% 1.77/0.59  fof(f134,plain,(
% 1.77/0.59    spl5_8 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.77/0.59  fof(f1197,plain,(
% 1.77/0.59    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_4 | ~spl5_6 | spl5_8)),
% 1.77/0.59    inference(forward_demodulation,[],[f136,f1007])).
% 1.77/0.59  fof(f136,plain,(
% 1.77/0.59    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_8),
% 1.77/0.59    inference(avatar_component_clause,[],[f134])).
% 1.77/0.59  fof(f1190,plain,(
% 1.77/0.59    ~spl5_30 | spl5_51 | spl5_118),
% 1.77/0.59    inference(avatar_split_clause,[],[f1185,f1180,f509,f367])).
% 1.77/0.59  fof(f1180,plain,(
% 1.77/0.59    spl5_118 <=> v4_relat_1(k7_relat_1(sK4,sK1),sK1)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 1.77/0.59  fof(f1185,plain,(
% 1.77/0.59    ( ! [X0] : (~v4_relat_1(sK4,X0) | ~v1_relat_1(sK4)) ) | spl5_118),
% 1.77/0.59    inference(resolution,[],[f1182,f84])).
% 1.77/0.59  fof(f84,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f42])).
% 1.77/0.59  fof(f1182,plain,(
% 1.77/0.59    ~v4_relat_1(k7_relat_1(sK4,sK1),sK1) | spl5_118),
% 1.77/0.59    inference(avatar_component_clause,[],[f1180])).
% 1.77/0.59  fof(f1183,plain,(
% 1.77/0.59    ~spl5_118 | ~spl5_102 | spl5_115),
% 1.77/0.59    inference(avatar_split_clause,[],[f1178,f1117,f1043,f1180])).
% 1.77/0.59  fof(f1117,plain,(
% 1.77/0.59    spl5_115 <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).
% 1.77/0.59  fof(f1178,plain,(
% 1.77/0.59    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~v4_relat_1(k7_relat_1(sK4,sK1),sK1) | spl5_115),
% 1.77/0.59    inference(resolution,[],[f1119,f65])).
% 1.77/0.59  fof(f1119,plain,(
% 1.77/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl5_115),
% 1.77/0.59    inference(avatar_component_clause,[],[f1117])).
% 1.77/0.59  fof(f1120,plain,(
% 1.77/0.59    ~spl5_115 | ~spl5_55 | ~spl5_102 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_30),
% 1.77/0.59    inference(avatar_split_clause,[],[f1115,f367,f130,f125,f115,f1043,f558,f1117])).
% 1.77/0.59  fof(f1115,plain,(
% 1.77/0.59    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | (~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_30)),
% 1.77/0.59    inference(forward_demodulation,[],[f1114,f1007])).
% 1.77/0.59  fof(f1114,plain,(
% 1.77/0.59    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_30)),
% 1.77/0.59    inference(forward_demodulation,[],[f1113,f380])).
% 1.77/0.59  fof(f1113,plain,(
% 1.77/0.59    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 1.77/0.59    inference(forward_demodulation,[],[f1112,f1007])).
% 1.77/0.59  fof(f1112,plain,(
% 1.77/0.59    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 1.77/0.59    inference(forward_demodulation,[],[f717,f1007])).
% 1.77/0.59  fof(f717,plain,(
% 1.77/0.59    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_7),
% 1.77/0.59    inference(resolution,[],[f132,f74])).
% 1.77/0.59  fof(f74,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f36])).
% 1.77/0.59  fof(f36,plain,(
% 1.77/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.77/0.59    inference(flattening,[],[f35])).
% 1.77/0.59  fof(f35,plain,(
% 1.77/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.77/0.59    inference(ennf_transformation,[],[f17])).
% 1.77/0.59  fof(f17,axiom,(
% 1.77/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.77/0.59  fof(f132,plain,(
% 1.77/0.59    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_7),
% 1.77/0.59    inference(avatar_component_clause,[],[f130])).
% 1.77/0.59  fof(f1046,plain,(
% 1.77/0.59    spl5_102 | ~spl5_4 | ~spl5_6 | ~spl5_56),
% 1.77/0.59    inference(avatar_split_clause,[],[f1015,f599,f125,f115,f1043])).
% 1.77/0.59  fof(f599,plain,(
% 1.77/0.59    spl5_56 <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 1.77/0.59  fof(f1015,plain,(
% 1.77/0.59    v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_4 | ~spl5_6 | ~spl5_56)),
% 1.77/0.59    inference(backward_demodulation,[],[f600,f1007])).
% 1.77/0.59  fof(f600,plain,(
% 1.77/0.59    v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~spl5_56),
% 1.77/0.59    inference(avatar_component_clause,[],[f599])).
% 1.77/0.59  fof(f945,plain,(
% 1.77/0.59    k1_xboole_0 != sK3 | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK3)),
% 1.77/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.77/0.59  fof(f816,plain,(
% 1.77/0.59    ~spl5_5 | spl5_77 | spl5_72 | ~spl5_4 | ~spl5_29),
% 1.77/0.59    inference(avatar_split_clause,[],[f811,f325,f115,f735,f813,f120])).
% 1.77/0.59  fof(f120,plain,(
% 1.77/0.59    spl5_5 <=> v1_funct_2(sK4,sK0,sK3)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.77/0.59  fof(f813,plain,(
% 1.77/0.59    spl5_77 <=> k1_xboole_0 = sK3),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 1.77/0.59  fof(f325,plain,(
% 1.77/0.59    spl5_29 <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.77/0.59  fof(f811,plain,(
% 1.77/0.59    sK0 = k1_relat_1(sK4) | k1_xboole_0 = sK3 | ~v1_funct_2(sK4,sK0,sK3) | (~spl5_4 | ~spl5_29)),
% 1.77/0.59    inference(forward_demodulation,[],[f807,f327])).
% 1.77/0.59  fof(f327,plain,(
% 1.77/0.59    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_29),
% 1.77/0.59    inference(avatar_component_clause,[],[f325])).
% 1.77/0.59  fof(f807,plain,(
% 1.77/0.59    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~v1_funct_2(sK4,sK0,sK3) | ~spl5_4),
% 1.77/0.59    inference(resolution,[],[f82,f117])).
% 1.77/0.59  fof(f82,plain,(
% 1.77/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f40])).
% 1.77/0.59  fof(f781,plain,(
% 1.77/0.59    ~spl5_4 | ~spl5_51),
% 1.77/0.59    inference(avatar_contradiction_clause,[],[f780])).
% 1.77/0.59  fof(f780,plain,(
% 1.77/0.59    $false | (~spl5_4 | ~spl5_51)),
% 1.77/0.59    inference(subsumption_resolution,[],[f117,f776])).
% 1.77/0.59  fof(f776,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_51),
% 1.77/0.59    inference(resolution,[],[f510,f76])).
% 1.77/0.59  fof(f510,plain,(
% 1.77/0.59    ( ! [X0] : (~v4_relat_1(sK4,X0)) ) | ~spl5_51),
% 1.77/0.59    inference(avatar_component_clause,[],[f509])).
% 1.77/0.59  fof(f677,plain,(
% 1.77/0.59    ~spl5_6 | ~spl5_4 | spl5_56),
% 1.77/0.59    inference(avatar_split_clause,[],[f670,f599,f115,f125])).
% 1.77/0.59  fof(f670,plain,(
% 1.77/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_56),
% 1.77/0.59    inference(resolution,[],[f89,f614])).
% 1.77/0.59  fof(f614,plain,(
% 1.77/0.59    ( ! [X2,X3] : (~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | spl5_56),
% 1.77/0.59    inference(resolution,[],[f611,f61])).
% 1.77/0.59  fof(f61,plain,(
% 1.77/0.59    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.77/0.59    inference(cnf_transformation,[],[f11])).
% 1.77/0.59  fof(f11,axiom,(
% 1.77/0.59    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.77/0.59  fof(f611,plain,(
% 1.77/0.59    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0))) ) | spl5_56),
% 1.77/0.59    inference(resolution,[],[f601,f58])).
% 1.77/0.59  fof(f58,plain,(
% 1.77/0.59    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f28])).
% 1.77/0.59  fof(f28,plain,(
% 1.77/0.59    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.77/0.59    inference(ennf_transformation,[],[f8])).
% 1.77/0.59  fof(f8,axiom,(
% 1.77/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.77/0.59  fof(f601,plain,(
% 1.77/0.59    ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_56),
% 1.77/0.59    inference(avatar_component_clause,[],[f599])).
% 1.77/0.59  fof(f89,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f47])).
% 1.77/0.59  fof(f561,plain,(
% 1.77/0.59    spl5_55 | ~spl5_2 | ~spl5_4),
% 1.77/0.59    inference(avatar_split_clause,[],[f556,f115,f105,f558])).
% 1.77/0.59  fof(f105,plain,(
% 1.77/0.59    spl5_2 <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.77/0.59  fof(f556,plain,(
% 1.77/0.59    r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl5_2 | ~spl5_4)),
% 1.77/0.59    inference(backward_demodulation,[],[f107,f550])).
% 1.77/0.59  fof(f550,plain,(
% 1.77/0.59    ( ! [X0] : (k9_relat_1(sK4,X0) = k7_relset_1(sK0,sK3,sK4,X0)) ) | ~spl5_4),
% 1.77/0.59    inference(resolution,[],[f86,f117])).
% 1.77/0.59  fof(f86,plain,(
% 1.77/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f43])).
% 1.77/0.59  fof(f43,plain,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.77/0.59    inference(ennf_transformation,[],[f16])).
% 1.77/0.59  fof(f16,axiom,(
% 1.77/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.77/0.59  fof(f107,plain,(
% 1.77/0.59    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) | ~spl5_2),
% 1.77/0.59    inference(avatar_component_clause,[],[f105])).
% 1.77/0.59  fof(f471,plain,(
% 1.77/0.59    ~spl5_41 | ~spl5_40 | spl5_44 | ~spl5_30 | ~spl5_39),
% 1.77/0.59    inference(avatar_split_clause,[],[f466,f438,f367,f468,f448,f452])).
% 1.77/0.59  fof(f468,plain,(
% 1.77/0.59    spl5_44 <=> v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k9_relat_1(sK4,k1_xboole_0))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.77/0.59  fof(f438,plain,(
% 1.77/0.59    spl5_39 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0))),
% 1.77/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.77/0.59  fof(f466,plain,(
% 1.77/0.59    v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k9_relat_1(sK4,k1_xboole_0)) | ~v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) | ~v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | (~spl5_30 | ~spl5_39)),
% 1.77/0.59    inference(forward_demodulation,[],[f444,f380])).
% 1.77/0.59  fof(f444,plain,(
% 1.77/0.59    v1_funct_2(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0,k2_relat_1(k7_relat_1(sK4,k1_xboole_0))) | ~v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) | ~v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | ~spl5_39),
% 1.77/0.59    inference(superposition,[],[f59,f440])).
% 1.77/0.59  fof(f440,plain,(
% 1.77/0.59    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | ~spl5_39),
% 1.77/0.59    inference(avatar_component_clause,[],[f438])).
% 1.77/0.59  fof(f59,plain,(
% 1.77/0.59    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f30])).
% 1.77/0.59  fof(f30,plain,(
% 1.77/0.59    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.77/0.59    inference(flattening,[],[f29])).
% 1.77/0.59  fof(f29,plain,(
% 1.77/0.59    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.77/0.59    inference(ennf_transformation,[],[f21])).
% 1.77/0.59  fof(f21,axiom,(
% 1.77/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.77/0.59  fof(f459,plain,(
% 1.77/0.59    ~spl5_40 | ~spl5_41 | spl5_42 | ~spl5_39),
% 1.77/0.59    inference(avatar_split_clause,[],[f446,f438,f456,f452,f448])).
% 1.77/0.59  fof(f446,plain,(
% 1.77/0.59    r1_tarski(k7_relat_1(sK4,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | ~v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) | ~spl5_39),
% 1.77/0.59    inference(forward_demodulation,[],[f442,f93])).
% 1.77/0.59  fof(f442,plain,(
% 1.77/0.59    r1_tarski(k7_relat_1(sK4,k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1(sK4,k1_xboole_0)))) | ~v1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | ~v1_funct_1(k7_relat_1(sK4,k1_xboole_0)) | ~spl5_39),
% 1.77/0.59    inference(superposition,[],[f257,f440])).
% 1.77/0.59  fof(f257,plain,(
% 1.77/0.59    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 1.77/0.59    inference(resolution,[],[f60,f70])).
% 1.77/0.59  fof(f70,plain,(
% 1.77/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f6])).
% 1.77/0.59  fof(f6,axiom,(
% 1.77/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.77/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.77/0.59  fof(f60,plain,(
% 1.77/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.77/0.59    inference(cnf_transformation,[],[f30])).
% 1.77/0.59  fof(f441,plain,(
% 1.77/0.59    spl5_39 | ~spl5_30),
% 1.77/0.59    inference(avatar_split_clause,[],[f430,f367,f438])).
% 1.77/0.59  fof(f430,plain,(
% 1.77/0.59    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | ~spl5_30),
% 1.77/0.59    inference(resolution,[],[f379,f56])).
% 1.77/0.60  fof(f377,plain,(
% 1.77/0.60    ~spl5_4 | spl5_30),
% 1.77/0.60    inference(avatar_contradiction_clause,[],[f375])).
% 1.77/0.60  fof(f375,plain,(
% 1.77/0.60    $false | (~spl5_4 | spl5_30)),
% 1.77/0.60    inference(unit_resulting_resolution,[],[f61,f117,f369,f58])).
% 1.77/0.60  fof(f369,plain,(
% 1.77/0.60    ~v1_relat_1(sK4) | spl5_30),
% 1.77/0.60    inference(avatar_component_clause,[],[f367])).
% 1.77/0.60  fof(f328,plain,(
% 1.77/0.60    spl5_29 | ~spl5_4),
% 1.77/0.60    inference(avatar_split_clause,[],[f318,f115,f325])).
% 1.77/0.60  fof(f318,plain,(
% 1.77/0.60    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_4),
% 1.77/0.60    inference(resolution,[],[f75,f117])).
% 1.77/0.60  fof(f146,plain,(
% 1.77/0.60    spl5_10),
% 1.77/0.60    inference(avatar_split_clause,[],[f55,f143])).
% 1.77/0.60  fof(f143,plain,(
% 1.77/0.60    spl5_10 <=> v1_xboole_0(k1_xboole_0)),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.77/0.60  fof(f55,plain,(
% 1.77/0.60    v1_xboole_0(k1_xboole_0)),
% 1.77/0.60    inference(cnf_transformation,[],[f1])).
% 1.77/0.60  fof(f1,axiom,(
% 1.77/0.60    v1_xboole_0(k1_xboole_0)),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.77/0.60  fof(f141,plain,(
% 1.77/0.60    ~spl5_7 | ~spl5_8 | ~spl5_9),
% 1.77/0.60    inference(avatar_split_clause,[],[f48,f138,f134,f130])).
% 1.77/0.60  fof(f48,plain,(
% 1.77/0.60    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.77/0.60    inference(cnf_transformation,[],[f27])).
% 1.77/0.60  fof(f27,plain,(
% 1.77/0.60    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.77/0.60    inference(flattening,[],[f26])).
% 1.77/0.60  fof(f26,plain,(
% 1.77/0.60    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.77/0.60    inference(ennf_transformation,[],[f23])).
% 1.77/0.60  fof(f23,negated_conjecture,(
% 1.77/0.60    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.77/0.60    inference(negated_conjecture,[],[f22])).
% 1.77/0.60  fof(f22,conjecture,(
% 1.77/0.60    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.77/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 1.77/0.60  fof(f128,plain,(
% 1.77/0.60    spl5_6),
% 1.77/0.60    inference(avatar_split_clause,[],[f49,f125])).
% 1.77/0.60  fof(f49,plain,(
% 1.77/0.60    v1_funct_1(sK4)),
% 1.77/0.60    inference(cnf_transformation,[],[f27])).
% 1.77/0.60  fof(f123,plain,(
% 1.77/0.60    spl5_5),
% 1.77/0.60    inference(avatar_split_clause,[],[f50,f120])).
% 1.77/0.60  fof(f50,plain,(
% 1.77/0.60    v1_funct_2(sK4,sK0,sK3)),
% 1.77/0.60    inference(cnf_transformation,[],[f27])).
% 1.77/0.60  fof(f118,plain,(
% 1.77/0.60    spl5_4),
% 1.77/0.60    inference(avatar_split_clause,[],[f51,f115])).
% 1.77/0.60  fof(f51,plain,(
% 1.77/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.77/0.60    inference(cnf_transformation,[],[f27])).
% 1.77/0.60  fof(f113,plain,(
% 1.77/0.60    spl5_3),
% 1.77/0.60    inference(avatar_split_clause,[],[f52,f110])).
% 1.77/0.60  fof(f52,plain,(
% 1.77/0.60    r1_tarski(sK1,sK0)),
% 1.77/0.60    inference(cnf_transformation,[],[f27])).
% 1.77/0.60  fof(f108,plain,(
% 1.77/0.60    spl5_2),
% 1.77/0.60    inference(avatar_split_clause,[],[f53,f105])).
% 1.77/0.60  fof(f53,plain,(
% 1.77/0.60    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.77/0.60    inference(cnf_transformation,[],[f27])).
% 1.77/0.60  fof(f103,plain,(
% 1.77/0.60    ~spl5_1),
% 1.77/0.60    inference(avatar_split_clause,[],[f54,f100])).
% 1.77/0.60  fof(f100,plain,(
% 1.77/0.60    spl5_1 <=> v1_xboole_0(sK3)),
% 1.77/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.77/0.60  fof(f54,plain,(
% 1.77/0.60    ~v1_xboole_0(sK3)),
% 1.77/0.60    inference(cnf_transformation,[],[f27])).
% 1.77/0.60  % SZS output end Proof for theBenchmark
% 1.77/0.60  % (3307)------------------------------
% 1.77/0.60  % (3307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.60  % (3307)Termination reason: Refutation
% 1.77/0.60  
% 1.77/0.60  % (3307)Memory used [KB]: 7547
% 1.77/0.60  % (3307)Time elapsed: 0.143 s
% 1.77/0.60  % (3307)------------------------------
% 1.77/0.60  % (3307)------------------------------
% 1.77/0.60  % (3288)Success in time 0.251 s
%------------------------------------------------------------------------------
