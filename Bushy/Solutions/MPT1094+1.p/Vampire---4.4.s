%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t29_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:13 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  540 (1833 expanded)
%              Number of leaves         :  116 ( 678 expanded)
%              Depth                    :   14
%              Number of atoms          : 1320 (3990 expanded)
%              Number of equality atoms :   49 ( 265 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1737,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f120,f127,f134,f147,f148,f165,f176,f187,f198,f230,f241,f256,f266,f277,f295,f302,f316,f327,f336,f343,f401,f412,f435,f444,f456,f470,f494,f506,f512,f518,f529,f541,f555,f567,f586,f598,f612,f623,f634,f659,f673,f685,f694,f708,f931,f961,f994,f995,f996,f997,f998,f999,f1000,f1001,f1002,f1004,f1005,f1006,f1007,f1008,f1009,f1010,f1011,f1012,f1013,f1014,f1015,f1016,f1017,f1018,f1021,f1052,f1068,f1087,f1111,f1136,f1155,f1168,f1175,f1184,f1185,f1233,f1247,f1263,f1278,f1400,f1416,f1425,f1432,f1439,f1448,f1455,f1504,f1521,f1530,f1609,f1634,f1641,f1650,f1651,f1720,f1736])).

fof(f1736,plain,
    ( ~ spl2_0
    | ~ spl2_8
    | spl2_11
    | ~ spl2_48 ),
    inference(avatar_contradiction_clause,[],[f1735])).

fof(f1735,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f1734,f112])).

fof(f112,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f1734,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f1733,f140])).

fof(f140,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl2_8
  <=> v1_finset_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f1733,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_11
    | ~ spl2_48 ),
    inference(subsumption_resolution,[],[f1731,f143])).

fof(f143,plain,
    ( ~ v1_finset_1(sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_11
  <=> ~ v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1731,plain,
    ( v1_finset_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_48 ),
    inference(resolution,[],[f1730,f411])).

fof(f411,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl2_48
  <=> v1_finset_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1730,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k2_relat_1(X0))
      | v1_finset_1(X0)
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f635,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t21_relat_1)).

fof(f635,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | v1_finset_1(X2)
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f209,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t3_subset)).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0)
      | v1_finset_1(X2) ) ),
    inference(resolution,[],[f95,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',cc2_finset_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k2_zfmisc_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X0) )
     => v1_finset_1(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',fc14_finset_1)).

fof(f1720,plain,
    ( spl2_156
    | ~ spl2_72 ),
    inference(avatar_split_clause,[],[f1710,f596,f1718])).

fof(f1718,plain,
    ( spl2_156
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_156])])).

fof(f596,plain,
    ( spl2_72
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f1710,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))))))))
    | ~ spl2_72 ),
    inference(resolution,[],[f599,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',existence_m1_subset_1)).

fof(f599,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0)))))))))
        | v1_finset_1(X0) )
    | ~ spl2_72 ),
    inference(resolution,[],[f597,f81])).

fof(f597,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))))))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f596])).

fof(f1651,plain,
    ( ~ spl2_153
    | spl2_125 ),
    inference(avatar_split_clause,[],[f1643,f1273,f1636])).

fof(f1636,plain,
    ( spl2_153
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_153])])).

fof(f1273,plain,
    ( spl2_125
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_125])])).

fof(f1643,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_125 ),
    inference(resolution,[],[f1274,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t1_subset)).

fof(f1274,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_125 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f1650,plain,
    ( ~ spl2_155
    | spl2_125 ),
    inference(avatar_split_clause,[],[f1642,f1273,f1648])).

fof(f1648,plain,
    ( spl2_155
  <=> ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_155])])).

fof(f1642,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK0)))
    | ~ spl2_125 ),
    inference(resolution,[],[f1274,f96])).

fof(f1641,plain,
    ( spl2_152
    | spl2_148
    | ~ spl2_124 ),
    inference(avatar_split_clause,[],[f1614,f1276,f1626,f1639])).

fof(f1639,plain,
    ( spl2_152
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_152])])).

fof(f1626,plain,
    ( spl2_148
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_148])])).

fof(f1276,plain,
    ( spl2_124
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_124])])).

fof(f1614,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_124 ),
    inference(resolution,[],[f1277,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t2_subset)).

fof(f1277,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_124 ),
    inference(avatar_component_clause,[],[f1276])).

fof(f1634,plain,
    ( spl2_148
    | ~ spl2_151
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f1617,f1245,f1632,f1626])).

fof(f1632,plain,
    ( spl2_151
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_151])])).

fof(f1245,plain,
    ( spl2_120
  <=> k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f1617,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_120 ),
    inference(superposition,[],[f203,f1246])).

fof(f1246,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f203,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f200,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',antisymmetry_r2_hidden)).

fof(f200,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f93,f84])).

fof(f1609,plain,
    ( spl2_146
    | ~ spl2_122 ),
    inference(avatar_split_clause,[],[f1599,f1261,f1607])).

fof(f1607,plain,
    ( spl2_146
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_146])])).

fof(f1261,plain,
    ( spl2_122
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_122])])).

fof(f1599,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))))))))
    | ~ spl2_122 ),
    inference(resolution,[],[f1280,f84])).

fof(f1280,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))))))))
        | v1_finset_1(X0) )
    | ~ spl2_122 ),
    inference(resolution,[],[f1262,f81])).

fof(f1262,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))))))
    | ~ spl2_122 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1530,plain,
    ( spl2_144
    | ~ spl2_84 ),
    inference(avatar_split_clause,[],[f699,f671,f1528])).

fof(f1528,plain,
    ( spl2_144
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_144])])).

fof(f671,plain,
    ( spl2_84
  <=> k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f699,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))
    | ~ spl2_84 ),
    inference(superposition,[],[f84,f672])).

fof(f672,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))
    | ~ spl2_84 ),
    inference(avatar_component_clause,[],[f671])).

fof(f1521,plain,
    ( spl2_142
    | ~ spl2_86 ),
    inference(avatar_split_clause,[],[f1511,f683,f1519])).

fof(f1519,plain,
    ( spl2_142
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_142])])).

fof(f683,plain,
    ( spl2_86
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f1511,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))))))))
    | ~ spl2_86 ),
    inference(resolution,[],[f710,f84])).

fof(f710,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))))))
        | v1_finset_1(X0) )
    | ~ spl2_86 ),
    inference(resolution,[],[f684,f81])).

fof(f684,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))))))
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f683])).

fof(f1504,plain,
    ( spl2_140
    | ~ spl2_70 ),
    inference(avatar_split_clause,[],[f1494,f584,f1502])).

fof(f1502,plain,
    ( spl2_140
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_140])])).

fof(f584,plain,
    ( spl2_70
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f1494,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))))))))
    | ~ spl2_70 ),
    inference(resolution,[],[f587,f84])).

fof(f587,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0)))))))))
        | v1_finset_1(X0) )
    | ~ spl2_70 ),
    inference(resolution,[],[f585,f81])).

fof(f585,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))))))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f584])).

fof(f1455,plain,
    ( ~ spl2_139
    | spl2_135 ),
    inference(avatar_split_clause,[],[f1441,f1437,f1453])).

fof(f1453,plain,
    ( spl2_139
  <=> ~ r2_hidden(k1_zfmisc_1(k1_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f1437,plain,
    ( spl2_135
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f1441,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_135 ),
    inference(resolution,[],[f1438,f92])).

fof(f1438,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_135 ),
    inference(avatar_component_clause,[],[f1437])).

fof(f1448,plain,
    ( ~ spl2_137
    | spl2_135 ),
    inference(avatar_split_clause,[],[f1440,f1437,f1446])).

fof(f1446,plain,
    ( spl2_137
  <=> ~ r1_tarski(k1_zfmisc_1(k1_relat_1(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_137])])).

fof(f1440,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_relat_1(sK0)),k1_xboole_0)
    | ~ spl2_135 ),
    inference(resolution,[],[f1438,f96])).

fof(f1439,plain,
    ( ~ spl2_135
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_128 ),
    inference(avatar_split_clause,[],[f1424,f1408,f264,f254,f1437])).

fof(f254,plain,
    ( spl2_24
  <=> v1_xboole_0(sK1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f264,plain,
    ( spl2_26
  <=> k1_xboole_0 = sK1(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1408,plain,
    ( spl2_128
  <=> r2_hidden(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_128])])).

fof(f1424,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_128 ),
    inference(forward_demodulation,[],[f1419,f265])).

fof(f265,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f264])).

fof(f1419,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_relat_1(sK0)),k1_zfmisc_1(sK1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl2_24
    | ~ spl2_128 ),
    inference(resolution,[],[f1409,f257])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl2_24 ),
    inference(resolution,[],[f255,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t5_subset)).

fof(f255,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f254])).

fof(f1409,plain,
    ( r2_hidden(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0)))
    | ~ spl2_128 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f1432,plain,
    ( ~ spl2_133
    | ~ spl2_128 ),
    inference(avatar_split_clause,[],[f1422,f1408,f1430])).

fof(f1430,plain,
    ( spl2_133
  <=> ~ r2_hidden(k1_zfmisc_1(k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_133])])).

fof(f1422,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl2_128 ),
    inference(resolution,[],[f1409,f91])).

fof(f1425,plain,
    ( ~ spl2_131
    | ~ spl2_128 ),
    inference(avatar_split_clause,[],[f1423,f1408,f1411])).

fof(f1411,plain,
    ( spl2_131
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).

fof(f1423,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_relat_1(sK0)))
    | ~ spl2_128 ),
    inference(resolution,[],[f1409,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t7_boole)).

fof(f1416,plain,
    ( spl2_128
    | spl2_130
    | ~ spl2_126 ),
    inference(avatar_split_clause,[],[f1403,f1398,f1414,f1408])).

fof(f1414,plain,
    ( spl2_130
  <=> v1_xboole_0(k1_zfmisc_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_130])])).

fof(f1398,plain,
    ( spl2_126
  <=> m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_126])])).

fof(f1403,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_relat_1(sK0)))
    | r2_hidden(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0)))
    | ~ spl2_126 ),
    inference(resolution,[],[f1399,f93])).

fof(f1399,plain,
    ( m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0)))
    | ~ spl2_126 ),
    inference(avatar_component_clause,[],[f1398])).

fof(f1400,plain,
    ( spl2_126
    | ~ spl2_60 ),
    inference(avatar_split_clause,[],[f1390,f504,f1398])).

fof(f504,plain,
    ( spl2_60
  <=> k1_relat_1(sK0) = k9_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f1390,plain,
    ( m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0)))
    | ~ spl2_60 ),
    inference(superposition,[],[f1348,f505])).

fof(f505,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1348,plain,(
    ! [X2,X0,X1] : m1_subset_1(k9_relat_1(k7_funct_3(X0,X1),X2),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f422,f571])).

fof(f571,plain,(
    ! [X10,X8,X9] : k7_relset_1(k2_zfmisc_1(X8,X9),X8,k7_funct_3(X8,X9),X10) = k9_relat_1(k7_funct_3(X8,X9),X10) ),
    inference(resolution,[],[f102,f105])).

fof(f105,plain,(
    ! [X0,X1] : m1_subset_1(k7_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0))) ),
    inference(forward_demodulation,[],[f88,f86])).

fof(f86,plain,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k7_funct_3(X0,X1) = k9_funct_3(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',redefinition_k9_funct_3)).

fof(f88,plain,(
    ! [X0,X1] : m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0)))
      & v1_funct_1(k9_funct_3(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(k9_funct_3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X0)))
      & v1_funct_2(k9_funct_3(X0,X1),k2_zfmisc_1(X0,X1),X0)
      & v1_funct_1(k9_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',dt_k9_funct_3)).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',redefinition_k7_relset_1)).

fof(f422,plain,(
    ! [X10,X8,X9] : m1_subset_1(k7_relset_1(k2_zfmisc_1(X8,X9),X8,k7_funct_3(X8,X9),X10),k1_zfmisc_1(X8)) ),
    inference(resolution,[],[f101,f105])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',dt_k7_relset_1)).

fof(f1278,plain,
    ( spl2_124
    | ~ spl2_120 ),
    inference(avatar_split_clause,[],[f1270,f1245,f1276])).

fof(f1270,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_120 ),
    inference(superposition,[],[f84,f1246])).

fof(f1263,plain,
    ( spl2_122
    | ~ spl2_118 ),
    inference(avatar_split_clause,[],[f1253,f1231,f1261])).

fof(f1231,plain,
    ( spl2_118
  <=> v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).

fof(f1253,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))))))
    | ~ spl2_118 ),
    inference(resolution,[],[f1248,f84])).

fof(f1248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))))))
        | v1_finset_1(X0) )
    | ~ spl2_118 ),
    inference(resolution,[],[f1232,f81])).

fof(f1232,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))))
    | ~ spl2_118 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1247,plain,
    ( spl2_120
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_116 ),
    inference(avatar_split_clause,[],[f1238,f1225,f264,f254,f1245])).

fof(f1225,plain,
    ( spl2_116
  <=> v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_116])])).

fof(f1238,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_116 ),
    inference(forward_demodulation,[],[f1234,f265])).

fof(f1234,plain,
    ( sK1(k1_zfmisc_1(k1_xboole_0)) = sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_24
    | ~ spl2_116 ),
    inference(resolution,[],[f1226,f258])).

fof(f258,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK1(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl2_24 ),
    inference(resolution,[],[f255,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t8_boole)).

fof(f1226,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))))
    | ~ spl2_116 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f1233,plain,
    ( spl2_116
    | spl2_118
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f534,f410,f1231,f1225])).

fof(f534,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0))))))
    | v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k2_relat_1(sK0)))))
    | ~ spl2_48 ),
    inference(resolution,[],[f517,f362])).

fof(f362,plain,(
    ! [X6] :
      ( m1_subset_1(sK1(sK1(k1_zfmisc_1(X6))),X6)
      | v1_xboole_0(sK1(k1_zfmisc_1(X6))) ) ),
    inference(resolution,[],[f350,f84])).

fof(f350,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK1(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f99,f200])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t4_subset)).

fof(f517,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK0)))
        | v1_finset_1(X0) )
    | ~ spl2_48 ),
    inference(resolution,[],[f411,f81])).

fof(f1185,plain,
    ( ~ spl2_113
    | spl2_103 ),
    inference(avatar_split_clause,[],[f1177,f1082,f1170])).

fof(f1170,plain,
    ( spl2_113
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).

fof(f1082,plain,
    ( spl2_103
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f1177,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_103 ),
    inference(resolution,[],[f1083,f92])).

fof(f1083,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_103 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1184,plain,
    ( ~ spl2_115
    | spl2_103 ),
    inference(avatar_split_clause,[],[f1176,f1082,f1182])).

fof(f1182,plain,
    ( spl2_115
  <=> ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).

fof(f1176,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_103 ),
    inference(resolution,[],[f1083,f96])).

fof(f1175,plain,
    ( spl2_112
    | spl2_108
    | ~ spl2_102 ),
    inference(avatar_split_clause,[],[f1141,f1085,f1160,f1173])).

fof(f1173,plain,
    ( spl2_112
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_112])])).

fof(f1160,plain,
    ( spl2_108
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_108])])).

fof(f1085,plain,
    ( spl2_102
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_102])])).

fof(f1141,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_102 ),
    inference(resolution,[],[f1086,f93])).

fof(f1086,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_102 ),
    inference(avatar_component_clause,[],[f1085])).

fof(f1168,plain,
    ( spl2_108
    | ~ spl2_111
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f1144,f1050,f1166,f1160])).

fof(f1166,plain,
    ( spl2_111
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_111])])).

fof(f1050,plain,
    ( spl2_98
  <=> k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f1144,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_98 ),
    inference(superposition,[],[f203,f1051])).

fof(f1051,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1155,plain,
    ( ~ spl2_107
    | ~ spl2_98
    | spl2_101 ),
    inference(avatar_split_clause,[],[f1148,f1063,f1050,f1153])).

fof(f1153,plain,
    ( spl2_107
  <=> ~ v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_107])])).

fof(f1063,plain,
    ( spl2_101
  <=> ~ v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_101])])).

fof(f1148,plain,
    ( ~ v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_xboole_0))))
    | ~ spl2_98
    | ~ spl2_101 ),
    inference(superposition,[],[f1064,f1051])).

fof(f1064,plain,
    ( ~ v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl2_101 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1136,plain,
    ( spl2_104
    | ~ spl2_100 ),
    inference(avatar_split_clause,[],[f1126,f1066,f1134])).

fof(f1134,plain,
    ( spl2_104
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_104])])).

fof(f1066,plain,
    ( spl2_100
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_100])])).

fof(f1126,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))))
    | ~ spl2_100 ),
    inference(resolution,[],[f1089,f84])).

fof(f1089,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))))
        | v1_finset_1(X0) )
    | ~ spl2_100 ),
    inference(resolution,[],[f1067,f81])).

fof(f1067,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl2_100 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f1111,plain,
    ( spl2_94
    | spl2_96
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f1036,f706,f959,f953])).

fof(f953,plain,
    ( spl2_94
  <=> v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).

fof(f959,plain,
    ( spl2_96
  <=> v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f706,plain,
    ( spl2_90
  <=> v1_finset_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f1036,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl2_90 ),
    inference(resolution,[],[f1022,f362])).

fof(f1022,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_finset_1(X0) )
    | ~ spl2_90 ),
    inference(resolution,[],[f707,f81])).

fof(f707,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f706])).

fof(f1087,plain,
    ( spl2_102
    | ~ spl2_98 ),
    inference(avatar_split_clause,[],[f1079,f1050,f1085])).

fof(f1079,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_98 ),
    inference(superposition,[],[f84,f1051])).

fof(f1068,plain,
    ( spl2_100
    | ~ spl2_96 ),
    inference(avatar_split_clause,[],[f1058,f959,f1066])).

fof(f1058,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))))
    | ~ spl2_96 ),
    inference(resolution,[],[f1053,f84])).

fof(f1053,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))))
        | v1_finset_1(X0) )
    | ~ spl2_96 ),
    inference(resolution,[],[f960,f81])).

fof(f960,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f959])).

fof(f1052,plain,
    ( spl2_98
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_94 ),
    inference(avatar_split_clause,[],[f1027,f953,f264,f254,f1050])).

fof(f1027,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_94 ),
    inference(forward_demodulation,[],[f1023,f265])).

fof(f1023,plain,
    ( sK1(k1_zfmisc_1(k1_xboole_0)) = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_24
    | ~ spl2_94 ),
    inference(resolution,[],[f954,f258])).

fof(f954,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl2_94 ),
    inference(avatar_component_clause,[],[f953])).

fof(f1021,plain,
    ( ~ spl2_8
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f962])).

fof(f962,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f140])).

fof(f930,plain,
    ( ! [X3] : ~ v1_finset_1(X3)
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f929])).

fof(f929,plain,
    ( spl2_92
  <=> ! [X3] : ~ v1_finset_1(X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f1018,plain,
    ( ~ spl2_8
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f967])).

fof(f967,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f741])).

fof(f741,plain,
    ( ! [X4,X3] : v1_finset_1(k9_relat_1(k7_funct_3(k1_relat_1(sK0),X3),X4))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f716,f571])).

fof(f716,plain,
    ( ! [X4,X3] : v1_finset_1(k7_relset_1(k2_zfmisc_1(k1_relat_1(sK0),X3),k1_relat_1(sK0),k7_funct_3(k1_relat_1(sK0),X3),X4))
    | ~ spl2_8 ),
    inference(resolution,[],[f422,f516])).

fof(f516,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(sK0)))
        | v1_finset_1(X0) )
    | ~ spl2_8 ),
    inference(resolution,[],[f140,f81])).

fof(f1017,plain,
    ( ~ spl2_48
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f968])).

fof(f968,plain,
    ( $false
    | ~ spl2_48
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f750])).

fof(f750,plain,
    ( ! [X33,X32] : v1_finset_1(k9_relat_1(k7_funct_3(k2_relat_1(sK0),X32),X33))
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f724,f571])).

fof(f724,plain,
    ( ! [X33,X32] : v1_finset_1(k7_relset_1(k2_zfmisc_1(k2_relat_1(sK0),X32),k2_relat_1(sK0),k7_funct_3(k2_relat_1(sK0),X32),X33))
    | ~ spl2_48 ),
    inference(resolution,[],[f422,f517])).

fof(f1016,plain,
    ( ~ spl2_62
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f969])).

fof(f969,plain,
    ( $false
    | ~ spl2_62
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f752])).

fof(f752,plain,
    ( ! [X37,X36] : v1_finset_1(k9_relat_1(k7_funct_3(sK1(k1_zfmisc_1(k1_relat_1(sK0))),X36),X37))
    | ~ spl2_62 ),
    inference(forward_demodulation,[],[f726,f571])).

fof(f726,plain,
    ( ! [X37,X36] : v1_finset_1(k7_relset_1(k2_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))),X36),sK1(k1_zfmisc_1(k1_relat_1(sK0))),k7_funct_3(sK1(k1_zfmisc_1(k1_relat_1(sK0))),X36),X37))
    | ~ spl2_62 ),
    inference(resolution,[],[f422,f530])).

fof(f530,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0)))))
        | v1_finset_1(X0) )
    | ~ spl2_62 ),
    inference(resolution,[],[f528,f81])).

fof(f528,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl2_62
  <=> v1_finset_1(sK1(k1_zfmisc_1(k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f1015,plain,
    ( ~ spl2_64
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f970])).

fof(f970,plain,
    ( $false
    | ~ spl2_64
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f755])).

fof(f755,plain,
    ( ! [X47,X46] : v1_finset_1(k9_relat_1(k7_funct_3(sK1(k1_zfmisc_1(k2_relat_1(sK0))),X46),X47))
    | ~ spl2_64 ),
    inference(forward_demodulation,[],[f729,f571])).

fof(f729,plain,
    ( ! [X47,X46] : v1_finset_1(k7_relset_1(k2_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))),X46),sK1(k1_zfmisc_1(k2_relat_1(sK0))),k7_funct_3(sK1(k1_zfmisc_1(k2_relat_1(sK0))),X46),X47))
    | ~ spl2_64 ),
    inference(resolution,[],[f422,f542])).

fof(f542,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0)))))
        | v1_finset_1(X0) )
    | ~ spl2_64 ),
    inference(resolution,[],[f540,f81])).

fof(f540,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl2_64
  <=> v1_finset_1(sK1(k1_zfmisc_1(k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f1014,plain,
    ( ~ spl2_66
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | ~ spl2_66
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f757])).

fof(f757,plain,
    ( ! [X50,X51] : v1_finset_1(k9_relat_1(k7_funct_3(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))),X50),X51))
    | ~ spl2_66 ),
    inference(forward_demodulation,[],[f731,f571])).

fof(f731,plain,
    ( ! [X50,X51] : v1_finset_1(k7_relset_1(k2_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))),X50),sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))),k7_funct_3(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))),X50),X51))
    | ~ spl2_66 ),
    inference(resolution,[],[f422,f556])).

fof(f556,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0)))))))
        | v1_finset_1(X0) )
    | ~ spl2_66 ),
    inference(resolution,[],[f554,f81])).

fof(f554,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))))
    | ~ spl2_66 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl2_66
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_66])])).

fof(f1013,plain,
    ( ~ spl2_68
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | ~ spl2_68
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f758])).

fof(f758,plain,
    ( ! [X52,X53] : v1_finset_1(k9_relat_1(k7_funct_3(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))),X52),X53))
    | ~ spl2_68 ),
    inference(forward_demodulation,[],[f732,f571])).

fof(f732,plain,
    ( ! [X52,X53] : v1_finset_1(k7_relset_1(k2_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))),X52),sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))),k7_funct_3(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))),X52),X53))
    | ~ spl2_68 ),
    inference(resolution,[],[f422,f568])).

fof(f568,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0)))))))
        | v1_finset_1(X0) )
    | ~ spl2_68 ),
    inference(resolution,[],[f566,f81])).

fof(f566,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))))
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl2_68
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f1012,plain,
    ( ~ spl2_82
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f973])).

fof(f973,plain,
    ( $false
    | ~ spl2_82
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f763])).

fof(f763,plain,
    ( ! [X62,X63] : v1_finset_1(k9_relat_1(k7_funct_3(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))),X62),X63))
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f737,f571])).

fof(f737,plain,
    ( ! [X62,X63] : v1_finset_1(k7_relset_1(k2_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))),X62),sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))),k7_funct_3(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))),X62),X63))
    | ~ spl2_82 ),
    inference(resolution,[],[f422,f709])).

fof(f709,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))))
        | v1_finset_1(X0) )
    | ~ spl2_82 ),
    inference(resolution,[],[f658,f81])).

fof(f658,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))))
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl2_82
  <=> v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f1011,plain,
    ( ~ spl2_8
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f841])).

fof(f841,plain,
    ( ! [X4,X3] : v1_finset_1(k9_relat_1(sK1(k1_zfmisc_1(k2_zfmisc_1(X3,k1_relat_1(sK0)))),X4))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f813,f572])).

fof(f572,plain,(
    ! [X12,X13,X11] : k7_relset_1(X11,X12,sK1(k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X13) = k9_relat_1(sK1(k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X13) ),
    inference(resolution,[],[f102,f84])).

fof(f813,plain,
    ( ! [X4,X3] : v1_finset_1(k7_relset_1(X3,k1_relat_1(sK0),sK1(k1_zfmisc_1(k2_zfmisc_1(X3,k1_relat_1(sK0)))),X4))
    | ~ spl2_8 ),
    inference(resolution,[],[f423,f516])).

fof(f423,plain,(
    ! [X12,X13,X11] : m1_subset_1(k7_relset_1(X11,X12,sK1(k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X13),k1_zfmisc_1(X12)) ),
    inference(resolution,[],[f101,f84])).

fof(f1010,plain,
    ( ~ spl2_48
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | ~ spl2_48
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f853])).

fof(f853,plain,
    ( ! [X45,X44] : v1_finset_1(k9_relat_1(sK1(k1_zfmisc_1(k2_zfmisc_1(X44,k2_relat_1(sK0)))),X45))
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f824,f572])).

fof(f824,plain,
    ( ! [X45,X44] : v1_finset_1(k7_relset_1(X44,k2_relat_1(sK0),sK1(k1_zfmisc_1(k2_zfmisc_1(X44,k2_relat_1(sK0)))),X45))
    | ~ spl2_48 ),
    inference(resolution,[],[f423,f517])).

fof(f1009,plain,
    ( ~ spl2_62
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f976])).

fof(f976,plain,
    ( $false
    | ~ spl2_62
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f855])).

fof(f855,plain,
    ( ! [X48,X49] : v1_finset_1(k9_relat_1(sK1(k1_zfmisc_1(k2_zfmisc_1(X48,sK1(k1_zfmisc_1(k1_relat_1(sK0)))))),X49))
    | ~ spl2_62 ),
    inference(forward_demodulation,[],[f826,f572])).

fof(f826,plain,
    ( ! [X48,X49] : v1_finset_1(k7_relset_1(X48,sK1(k1_zfmisc_1(k1_relat_1(sK0))),sK1(k1_zfmisc_1(k2_zfmisc_1(X48,sK1(k1_zfmisc_1(k1_relat_1(sK0)))))),X49))
    | ~ spl2_62 ),
    inference(resolution,[],[f423,f530])).

fof(f1008,plain,
    ( ~ spl2_64
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f977])).

fof(f977,plain,
    ( $false
    | ~ spl2_64
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f858])).

fof(f858,plain,
    ( ! [X59,X58] : v1_finset_1(k9_relat_1(sK1(k1_zfmisc_1(k2_zfmisc_1(X58,sK1(k1_zfmisc_1(k2_relat_1(sK0)))))),X59))
    | ~ spl2_64 ),
    inference(forward_demodulation,[],[f829,f572])).

fof(f829,plain,
    ( ! [X59,X58] : v1_finset_1(k7_relset_1(X58,sK1(k1_zfmisc_1(k2_relat_1(sK0))),sK1(k1_zfmisc_1(k2_zfmisc_1(X58,sK1(k1_zfmisc_1(k2_relat_1(sK0)))))),X59))
    | ~ spl2_64 ),
    inference(resolution,[],[f423,f542])).

fof(f1007,plain,
    ( ~ spl2_8
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f979])).

fof(f979,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f799])).

fof(f799,plain,
    ( ! [X6,X8,X7,X9] : v1_finset_1(k9_relat_1(k7_funct_3(k9_relat_1(k7_funct_3(k1_relat_1(sK0),X6),X7),X8),X9))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f795,f571])).

fof(f795,plain,
    ( ! [X6,X8,X7,X9] : v1_finset_1(k7_relset_1(k2_zfmisc_1(k9_relat_1(k7_funct_3(k1_relat_1(sK0),X6),X7),X8),k9_relat_1(k7_funct_3(k1_relat_1(sK0),X6),X7),k7_funct_3(k9_relat_1(k7_funct_3(k1_relat_1(sK0),X6),X7),X8),X9))
    | ~ spl2_8 ),
    inference(resolution,[],[f766,f422])).

fof(f766,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k9_relat_1(k7_funct_3(k1_relat_1(sK0),X1),X2)))
        | v1_finset_1(X0) )
    | ~ spl2_8 ),
    inference(resolution,[],[f741,f81])).

fof(f1006,plain,
    ( ~ spl2_48
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f980])).

fof(f980,plain,
    ( $false
    | ~ spl2_48
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f808])).

fof(f808,plain,
    ( ! [X6,X8,X7,X9] : v1_finset_1(k9_relat_1(k7_funct_3(k9_relat_1(k7_funct_3(k2_relat_1(sK0),X6),X7),X8),X9))
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f805,f571])).

fof(f805,plain,
    ( ! [X6,X8,X7,X9] : v1_finset_1(k7_relset_1(k2_zfmisc_1(k9_relat_1(k7_funct_3(k2_relat_1(sK0),X6),X7),X8),k9_relat_1(k7_funct_3(k2_relat_1(sK0),X6),X7),k7_funct_3(k9_relat_1(k7_funct_3(k2_relat_1(sK0),X6),X7),X8),X9))
    | ~ spl2_48 ),
    inference(resolution,[],[f768,f422])).

fof(f768,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k9_relat_1(k7_funct_3(k2_relat_1(sK0),X1),X2)))
        | v1_finset_1(X0) )
    | ~ spl2_48 ),
    inference(resolution,[],[f750,f81])).

fof(f1005,plain,
    ( ~ spl2_48
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | ~ spl2_48
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f411])).

fof(f1004,plain,
    ( ~ spl2_62
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f982])).

fof(f982,plain,
    ( $false
    | ~ spl2_62
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f528])).

fof(f1002,plain,
    ( ~ spl2_8
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f985])).

fof(f985,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f796])).

fof(f796,plain,
    ( ! [X10,X11] : v1_finset_1(sK1(k1_zfmisc_1(k9_relat_1(k7_funct_3(k1_relat_1(sK0),X10),X11))))
    | ~ spl2_8 ),
    inference(resolution,[],[f766,f84])).

fof(f1001,plain,
    ( ~ spl2_48
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f986])).

fof(f986,plain,
    ( $false
    | ~ spl2_48
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f806])).

fof(f806,plain,
    ( ! [X10,X11] : v1_finset_1(sK1(k1_zfmisc_1(k9_relat_1(k7_funct_3(k2_relat_1(sK0),X10),X11))))
    | ~ spl2_48 ),
    inference(resolution,[],[f768,f84])).

fof(f1000,plain,
    ( ~ spl2_64
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f987])).

fof(f987,plain,
    ( $false
    | ~ spl2_64
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f540])).

fof(f999,plain,
    ( ~ spl2_66
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f988])).

fof(f988,plain,
    ( $false
    | ~ spl2_66
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f554])).

fof(f998,plain,
    ( ~ spl2_68
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | ~ spl2_68
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f566])).

fof(f997,plain,
    ( ~ spl2_72
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f990])).

fof(f990,plain,
    ( $false
    | ~ spl2_72
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f597])).

fof(f996,plain,
    ( ~ spl2_70
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f991])).

fof(f991,plain,
    ( $false
    | ~ spl2_70
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f585])).

fof(f995,plain,
    ( ~ spl2_86
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f992])).

fof(f992,plain,
    ( $false
    | ~ spl2_86
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f684])).

fof(f994,plain,
    ( ~ spl2_82
    | ~ spl2_92 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | ~ spl2_82
    | ~ spl2_92 ),
    inference(resolution,[],[f930,f658])).

fof(f961,plain,
    ( spl2_94
    | spl2_96
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f939,f706,f959,f953])).

fof(f939,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl2_90 ),
    inference(resolution,[],[f932,f362])).

fof(f932,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_finset_1(X0) )
    | ~ spl2_90 ),
    inference(resolution,[],[f707,f81])).

fof(f931,plain,
    ( spl2_92
    | spl2_90
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f927,f264,f254,f125,f706,f929])).

fof(f125,plain,
    ( spl2_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f927,plain,
    ( ! [X3] :
        ( v1_finset_1(k1_xboole_0)
        | ~ v1_finset_1(X3) )
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f926,f89])).

fof(f89,plain,(
    ! [X0,X1] : v1_relat_1(k7_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_funct_1(k7_funct_3(X0,X1))
      & v1_relat_1(k7_funct_3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',dt_k7_funct_3)).

fof(f926,plain,
    ( ! [X2,X3] :
        ( v1_finset_1(k1_xboole_0)
        | ~ v1_finset_1(X3)
        | ~ v1_relat_1(k7_funct_3(k1_xboole_0,X2)) )
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f925,f106])).

fof(f106,plain,(
    ! [X0,X1] : v1_funct_1(k7_funct_3(X0,X1)) ),
    inference(forward_demodulation,[],[f87,f86])).

fof(f87,plain,(
    ! [X0,X1] : v1_funct_1(k9_funct_3(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f925,plain,
    ( ! [X2,X3] :
        ( v1_finset_1(k1_xboole_0)
        | ~ v1_finset_1(X3)
        | ~ v1_funct_1(k7_funct_3(k1_xboole_0,X2))
        | ~ v1_relat_1(k7_funct_3(k1_xboole_0,X2)) )
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(superposition,[],[f94,f774])).

fof(f774,plain,
    ( ! [X0,X1] : k1_xboole_0 = k9_relat_1(k7_funct_3(k1_xboole_0,X0),X1)
    | ~ spl2_4
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f770,f265])).

fof(f770,plain,
    ( ! [X0,X1] : k9_relat_1(k7_funct_3(k1_xboole_0,X0),X1) = sK1(k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_24 ),
    inference(resolution,[],[f742,f258])).

fof(f742,plain,
    ( ! [X6,X5] : v1_xboole_0(k9_relat_1(k7_funct_3(k1_xboole_0,X5),X6))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f717,f571])).

fof(f717,plain,
    ( ! [X6,X5] : v1_xboole_0(k7_relset_1(k2_zfmisc_1(k1_xboole_0,X5),k1_xboole_0,k7_funct_3(k1_xboole_0,X5),X6))
    | ~ spl2_4 ),
    inference(resolution,[],[f422,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f245,f200])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f100,f126])).

fof(f126,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k9_relat_1(X0,X1))
      | ~ v1_finset_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v1_finset_1(k9_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',fc13_finset_1)).

fof(f708,plain,
    ( spl2_90
    | ~ spl2_8
    | ~ spl2_84 ),
    inference(avatar_split_clause,[],[f700,f671,f139,f706])).

fof(f700,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_84 ),
    inference(subsumption_resolution,[],[f695,f140])).

fof(f695,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ v1_finset_1(k1_relat_1(sK0))
    | ~ spl2_84 ),
    inference(superposition,[],[f344,f672])).

fof(f344,plain,(
    ! [X0] :
      ( v1_finset_1(sK1(k1_zfmisc_1(k1_zfmisc_1(X0))))
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f158,f84])).

fof(f158,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | v1_finset_1(X1)
      | ~ v1_finset_1(X2) ) ),
    inference(resolution,[],[f81,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',fc17_finset_1)).

fof(f694,plain,
    ( ~ spl2_89
    | spl2_83
    | ~ spl2_84 ),
    inference(avatar_split_clause,[],[f686,f671,f654,f692])).

fof(f692,plain,
    ( spl2_89
  <=> ~ v1_finset_1(sK1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f654,plain,
    ( spl2_83
  <=> ~ v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f686,plain,
    ( ~ v1_finset_1(sK1(k1_xboole_0))
    | ~ spl2_83
    | ~ spl2_84 ),
    inference(forward_demodulation,[],[f655,f672])).

fof(f655,plain,
    ( ~ v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))))
    | ~ spl2_83 ),
    inference(avatar_component_clause,[],[f654])).

fof(f685,plain,
    ( spl2_86
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f677,f657,f683])).

fof(f677,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))))))
    | ~ spl2_82 ),
    inference(resolution,[],[f674,f84])).

fof(f674,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))))
        | v1_finset_1(X0) )
    | ~ spl2_82 ),
    inference(resolution,[],[f658,f81])).

fof(f673,plain,
    ( spl2_84
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f664,f651,f264,f254,f671])).

fof(f651,plain,
    ( spl2_80
  <=> v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f664,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f660,f265])).

fof(f660,plain,
    ( sK1(k1_zfmisc_1(k1_xboole_0)) = sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))
    | ~ spl2_24
    | ~ spl2_80 ),
    inference(resolution,[],[f652,f258])).

fof(f652,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f651])).

fof(f659,plain,
    ( spl2_80
    | spl2_82
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f522,f139,f657,f651])).

fof(f522,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0))))))
    | v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK0)))))
    | ~ spl2_8 ),
    inference(resolution,[],[f516,f362])).

fof(f634,plain,
    ( spl2_78
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f626,f454,f632])).

fof(f632,plain,
    ( spl2_78
  <=> v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_78])])).

fof(f454,plain,
    ( spl2_54
  <=> v1_relat_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f626,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))))))
    | ~ spl2_54 ),
    inference(resolution,[],[f472,f84])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))))
        | v1_relat_1(X0) )
    | ~ spl2_54 ),
    inference(resolution,[],[f455,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',cc2_relat_1)).

fof(f455,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f454])).

fof(f623,plain,
    ( spl2_76
    | ~ spl2_50 ),
    inference(avatar_split_clause,[],[f615,f433,f621])).

fof(f621,plain,
    ( spl2_76
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f433,plain,
    ( spl2_50
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f615,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))))))
    | ~ spl2_50 ),
    inference(resolution,[],[f436,f84])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))))
        | v1_finset_1(X0) )
    | ~ spl2_50 ),
    inference(resolution,[],[f434,f81])).

fof(f434,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_50 ),
    inference(avatar_component_clause,[],[f433])).

fof(f612,plain,
    ( spl2_74
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f604,f239,f610])).

fof(f610,plain,
    ( spl2_74
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f239,plain,
    ( spl2_22
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f604,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))))))
    | ~ spl2_22 ),
    inference(resolution,[],[f242,f84])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))))
        | v1_finset_1(X0) )
    | ~ spl2_22 ),
    inference(resolution,[],[f240,f81])).

fof(f240,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f239])).

fof(f598,plain,
    ( spl2_72
    | ~ spl2_68 ),
    inference(avatar_split_clause,[],[f590,f565,f596])).

fof(f590,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))))))
    | ~ spl2_68 ),
    inference(resolution,[],[f568,f84])).

fof(f586,plain,
    ( spl2_70
    | ~ spl2_66 ),
    inference(avatar_split_clause,[],[f578,f553,f584])).

fof(f578,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))))))
    | ~ spl2_66 ),
    inference(resolution,[],[f556,f84])).

fof(f567,plain,
    ( spl2_68
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f559,f539,f565])).

fof(f559,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))))
    | ~ spl2_64 ),
    inference(resolution,[],[f542,f84])).

fof(f555,plain,
    ( spl2_66
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f547,f527,f553])).

fof(f547,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))))
    | ~ spl2_62 ),
    inference(resolution,[],[f530,f84])).

fof(f541,plain,
    ( spl2_64
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f533,f410,f539])).

fof(f533,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(k2_relat_1(sK0))))
    | ~ spl2_48 ),
    inference(resolution,[],[f517,f84])).

fof(f529,plain,
    ( spl2_62
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f521,f139,f527])).

fof(f521,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(k1_relat_1(sK0))))
    | ~ spl2_8 ),
    inference(resolution,[],[f516,f84])).

fof(f518,plain,
    ( ~ spl2_11
    | spl2_8
    | ~ spl2_60 ),
    inference(avatar_split_clause,[],[f514,f504,f139,f142])).

fof(f514,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ v1_finset_1(sK0)
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f513,f89])).

fof(f513,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ v1_finset_1(sK0)
    | ~ v1_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f507,f106])).

fof(f507,plain,
    ( v1_finset_1(k1_relat_1(sK0))
    | ~ v1_finset_1(sK0)
    | ~ v1_funct_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_60 ),
    inference(superposition,[],[f94,f505])).

fof(f512,plain,
    ( spl2_9
    | ~ spl2_10
    | ~ spl2_60 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f510,f89])).

fof(f510,plain,
    ( ~ v1_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f509,f106])).

fof(f509,plain,
    ( ~ v1_funct_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f508,f146])).

fof(f146,plain,
    ( v1_finset_1(sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl2_10
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f508,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_funct_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_9
    | ~ spl2_60 ),
    inference(subsumption_resolution,[],[f507,f137])).

fof(f137,plain,
    ( ~ v1_finset_1(k1_relat_1(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_9
  <=> ~ v1_finset_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f506,plain,
    ( spl2_60
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f498,f118,f111,f504])).

fof(f118,plain,
    ( spl2_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f498,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f496,f112])).

fof(f496,plain,
    ( k1_relat_1(sK0) = k9_relat_1(k7_funct_3(k1_relat_1(sK0),k2_relat_1(sK0)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f104,f119])).

fof(f119,plain,
    ( v1_funct_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) = k9_relat_1(k7_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f82,f86])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => k1_relat_1(X0) = k9_relat_1(k9_funct_3(k1_relat_1(X0),k2_relat_1(X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t100_funct_3)).

fof(f494,plain,
    ( spl2_58
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f486,f228,f492])).

fof(f492,plain,
    ( spl2_58
  <=> v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f228,plain,
    ( spl2_20
  <=> v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f486,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))))))
    | ~ spl2_20 ),
    inference(resolution,[],[f231,f84])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))))
        | v1_relat_1(X0) )
    | ~ spl2_20 ),
    inference(resolution,[],[f229,f79])).

fof(f229,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f228])).

fof(f470,plain,
    ( spl2_56
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f461,f399,f264,f254,f468])).

fof(f468,plain,
    ( spl2_56
  <=> k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f399,plain,
    ( spl2_46
  <=> v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f461,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f457,f265])).

fof(f457,plain,
    ( sK1(k1_zfmisc_1(k1_xboole_0)) = sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_24
    | ~ spl2_46 ),
    inference(resolution,[],[f400,f258])).

fof(f400,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f399])).

fof(f456,plain,
    ( spl2_54
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f448,f442,f454])).

fof(f442,plain,
    ( spl2_52
  <=> v1_relat_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f448,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_52 ),
    inference(resolution,[],[f445,f84])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))
        | v1_relat_1(X0) )
    | ~ spl2_52 ),
    inference(resolution,[],[f443,f79])).

fof(f443,plain,
    ( v1_relat_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f442])).

fof(f444,plain,
    ( spl2_52
    | spl2_46
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f380,f111,f399,f442])).

fof(f380,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))
    | v1_relat_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))
    | ~ spl2_0 ),
    inference(resolution,[],[f362,f151])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_relat_1(X0) )
    | ~ spl2_0 ),
    inference(resolution,[],[f79,f112])).

fof(f435,plain,
    ( spl2_50
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f427,f393,f433])).

fof(f393,plain,
    ( spl2_44
  <=> v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f427,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_44 ),
    inference(resolution,[],[f419,f84])).

fof(f419,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))))
        | v1_finset_1(X0) )
    | ~ spl2_44 ),
    inference(resolution,[],[f394,f81])).

fof(f394,plain,
    ( v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f393])).

fof(f412,plain,
    ( spl2_48
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f405,f139,f118,f111,f410])).

fof(f405,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ spl2_0
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f404,f112])).

fof(f404,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f402,f119])).

fof(f402,plain,
    ( v1_finset_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl2_8 ),
    inference(resolution,[],[f140,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k1_relat_1(X0))
      | v1_finset_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_finset_1(k2_relat_1(X0))
      | ~ v1_finset_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
       => v1_finset_1(k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t26_finset_1)).

fof(f401,plain,
    ( spl2_44
    | spl2_46
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f379,f145,f399,f393])).

fof(f379,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0))))
    | v1_finset_1(sK1(sK1(k1_zfmisc_1(k1_zfmisc_1(sK0)))))
    | ~ spl2_10 ),
    inference(resolution,[],[f362,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_finset_1(X0) )
    | ~ spl2_10 ),
    inference(resolution,[],[f81,f146])).

fof(f343,plain,
    ( ~ spl2_43
    | spl2_39 ),
    inference(avatar_split_clause,[],[f329,f325,f341])).

fof(f341,plain,
    ( spl2_43
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f325,plain,
    ( spl2_39
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f329,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_39 ),
    inference(resolution,[],[f326,f92])).

fof(f326,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f325])).

fof(f336,plain,
    ( ~ spl2_41
    | spl2_39 ),
    inference(avatar_split_clause,[],[f328,f325,f334])).

fof(f334,plain,
    ( spl2_41
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f328,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_39 ),
    inference(resolution,[],[f326,f96])).

fof(f327,plain,
    ( ~ spl2_39
    | ~ spl2_4
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f318,f300,f125,f325])).

fof(f300,plain,
    ( spl2_34
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f318,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_34 ),
    inference(resolution,[],[f301,f245])).

fof(f301,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f300])).

fof(f316,plain,
    ( spl2_36
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f307,f287,f264,f254,f314])).

fof(f314,plain,
    ( spl2_36
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f287,plain,
    ( spl2_30
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f307,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl2_24
    | ~ spl2_26
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f303,f265])).

fof(f303,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK1(k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_24
    | ~ spl2_30 ),
    inference(resolution,[],[f288,f258])).

fof(f288,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f287])).

fof(f302,plain,
    ( spl2_30
    | spl2_34
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f269,f264,f300,f287])).

fof(f269,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_26 ),
    inference(superposition,[],[f200,f265])).

fof(f295,plain,
    ( spl2_30
    | ~ spl2_33
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f268,f264,f293,f287])).

fof(f293,plain,
    ( spl2_33
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f268,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_26 ),
    inference(superposition,[],[f203,f265])).

fof(f277,plain,
    ( spl2_28
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f270,f264,f275])).

fof(f275,plain,
    ( spl2_28
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f270,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_26 ),
    inference(superposition,[],[f84,f265])).

fof(f266,plain,
    ( spl2_26
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f259,f254,f264])).

fof(f259,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_24 ),
    inference(resolution,[],[f255,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t6_boole)).

fof(f256,plain,
    ( spl2_24
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f247,f125,f254])).

fof(f247,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f246,f84])).

fof(f241,plain,
    ( spl2_22
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f232,f196,f239])).

fof(f196,plain,
    ( spl2_18
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f232,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_18 ),
    inference(resolution,[],[f199,f84])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))
        | v1_finset_1(X0) )
    | ~ spl2_18 ),
    inference(resolution,[],[f197,f81])).

fof(f197,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f230,plain,
    ( spl2_20
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f221,f185,f228])).

fof(f185,plain,
    ( spl2_16
  <=> v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f221,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))))
    | ~ spl2_16 ),
    inference(resolution,[],[f188,f84])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))))
        | v1_relat_1(X0) )
    | ~ spl2_16 ),
    inference(resolution,[],[f186,f79])).

fof(f186,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f198,plain,
    ( spl2_18
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f189,f174,f196])).

fof(f174,plain,
    ( spl2_14
  <=> v1_finset_1(sK1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f189,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))
    | ~ spl2_14 ),
    inference(resolution,[],[f177,f84])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))
        | v1_finset_1(X0) )
    | ~ spl2_14 ),
    inference(resolution,[],[f175,f81])).

fof(f175,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK0)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f187,plain,
    ( spl2_16
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f178,f163,f185])).

fof(f163,plain,
    ( spl2_12
  <=> v1_relat_1(sK1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f178,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK1(k1_zfmisc_1(sK0)))))
    | ~ spl2_12 ),
    inference(resolution,[],[f166,f84])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1(k1_zfmisc_1(sK0))))
        | v1_relat_1(X0) )
    | ~ spl2_12 ),
    inference(resolution,[],[f164,f79])).

fof(f164,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f176,plain,
    ( spl2_14
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f167,f145,f174])).

fof(f167,plain,
    ( v1_finset_1(sK1(k1_zfmisc_1(sK0)))
    | ~ spl2_10 ),
    inference(resolution,[],[f157,f84])).

fof(f165,plain,
    ( spl2_12
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f154,f111,f163])).

fof(f154,plain,
    ( v1_relat_1(sK1(k1_zfmisc_1(sK0)))
    | ~ spl2_0 ),
    inference(resolution,[],[f151,f84])).

fof(f148,plain,
    ( ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f74,f142,f136])).

fof(f74,plain,
    ( ~ v1_finset_1(sK0)
    | ~ v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ( ~ v1_finset_1(sK0)
      | ~ v1_finset_1(k1_relat_1(sK0)) )
    & ( v1_finset_1(sK0)
      | v1_finset_1(k1_relat_1(sK0)) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f66,f67])).

fof(f67,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(X0)
          | ~ v1_finset_1(k1_relat_1(X0)) )
        & ( v1_finset_1(X0)
          | v1_finset_1(k1_relat_1(X0)) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v1_finset_1(sK0)
        | ~ v1_finset_1(k1_relat_1(sK0)) )
      & ( v1_finset_1(sK0)
        | v1_finset_1(k1_relat_1(sK0)) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(X0)
        | ~ v1_finset_1(k1_relat_1(X0)) )
      & ( v1_finset_1(X0)
        | v1_finset_1(k1_relat_1(X0)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ( v1_finset_1(k1_relat_1(X0))
      <~> v1_finset_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v1_finset_1(k1_relat_1(X0))
        <=> v1_finset_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_finset_1(k1_relat_1(X0))
      <=> v1_finset_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t29_finset_1)).

fof(f147,plain,
    ( spl2_8
    | spl2_10 ),
    inference(avatar_split_clause,[],[f73,f145,f139])).

fof(f73,plain,
    ( v1_finset_1(sK0)
    | v1_finset_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f134,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f76,f132])).

fof(f132,plain,
    ( spl2_6
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f76,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',d2_xboole_0)).

fof(f127,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f103,f125])).

fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f75,f76])).

fof(f75,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',dt_o_0_0_xboole_0)).

fof(f120,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f72,f118])).

fof(f72,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f113,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f71,f111])).

fof(f71,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
