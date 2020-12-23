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
% DateTime   : Thu Dec  3 13:03:12 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 474 expanded)
%              Number of leaves         :   52 ( 195 expanded)
%              Depth                    :   11
%              Number of atoms          :  739 (1561 expanded)
%              Number of equality atoms :  129 ( 319 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f115,f120,f125,f130,f136,f145,f153,f164,f202,f214,f266,f324,f326,f334,f343,f349,f503,f525,f654,f688,f710,f721,f785,f794,f817,f864,f892,f981,f1001,f1116,f1149,f1153,f1484,f1520,f1531,f1549,f1557])).

fof(f1557,plain,
    ( spl4_8
    | spl4_71
    | ~ spl4_73
    | ~ spl4_144 ),
    inference(avatar_contradiction_clause,[],[f1556])).

fof(f1556,plain,
    ( $false
    | spl4_8
    | spl4_71
    | ~ spl4_73
    | ~ spl4_144 ),
    inference(subsumption_resolution,[],[f1555,f815])).

fof(f815,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_73 ),
    inference(avatar_component_clause,[],[f814])).

fof(f814,plain,
    ( spl4_73
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1555,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_8
    | spl4_71
    | ~ spl4_144 ),
    inference(subsumption_resolution,[],[f1554,f140])).

fof(f140,plain,
    ( k1_xboole_0 != sK1
    | spl4_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1554,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_71
    | ~ spl4_144 ),
    inference(subsumption_resolution,[],[f1552,f805])).

fof(f805,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_71 ),
    inference(avatar_component_clause,[],[f804])).

fof(f804,plain,
    ( spl4_71
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1552,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_144 ),
    inference(trivial_inequality_removal,[],[f1551])).

fof(f1551,plain,
    ( sK2 != sK2
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_144 ),
    inference(superposition,[],[f86,f1548])).

fof(f1548,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_144 ),
    inference(avatar_component_clause,[],[f1546])).

fof(f1546,plain,
    ( spl4_144
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1549,plain,
    ( spl4_144
    | ~ spl4_73
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1542,f1146,f814,f1546])).

fof(f1146,plain,
    ( spl4_108
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1542,plain,
    ( sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_73
    | ~ spl4_108 ),
    inference(forward_demodulation,[],[f1536,f1148])).

fof(f1148,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1536,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_73 ),
    inference(resolution,[],[f815,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1531,plain,
    ( spl4_73
    | ~ spl4_109
    | ~ spl4_143 ),
    inference(avatar_contradiction_clause,[],[f1530])).

fof(f1530,plain,
    ( $false
    | spl4_73
    | ~ spl4_109
    | ~ spl4_143 ),
    inference(subsumption_resolution,[],[f1524,f816])).

fof(f816,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_73 ),
    inference(avatar_component_clause,[],[f814])).

fof(f1524,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_109
    | ~ spl4_143 ),
    inference(resolution,[],[f1519,f1152])).

fof(f1152,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) )
    | ~ spl4_109 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f1151,plain,
    ( spl4_109
  <=> ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f1519,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_143 ),
    inference(avatar_component_clause,[],[f1518])).

fof(f1518,plain,
    ( spl4_143
  <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f1520,plain,
    ( spl4_143
    | ~ spl4_82
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f1503,f1464,f890,f1518])).

fof(f890,plain,
    ( spl4_82
  <=> ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f1464,plain,
    ( spl4_138
  <=> ! [X5,X4] :
        ( ~ v5_relat_1(k7_relat_1(sK3,X4),X5)
        | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f1503,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_82
    | ~ spl4_138 ),
    inference(resolution,[],[f1465,f891])).

fof(f891,plain,
    ( ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1)
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f890])).

fof(f1465,plain,
    ( ! [X4,X5] :
        ( ~ v5_relat_1(k7_relat_1(sK3,X4),X5)
        | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5) )
    | ~ spl4_138 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f1484,plain,
    ( spl4_138
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f657,f200,f1464])).

fof(f200,plain,
    ( spl4_14
  <=> ! [X2] : v1_relat_1(k7_relat_1(sK3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f657,plain,
    ( ! [X4,X5] :
        ( ~ v5_relat_1(k7_relat_1(sK3,X4),X5)
        | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5) )
    | ~ spl4_14 ),
    inference(resolution,[],[f201,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f201,plain,
    ( ! [X2] : v1_relat_1(k7_relat_1(sK3,X2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f200])).

fof(f1153,plain,
    ( spl4_109
    | ~ spl4_3
    | ~ spl4_93
    | ~ spl4_104 ),
    inference(avatar_split_clause,[],[f1144,f1114,f999,f112,f1151])).

fof(f112,plain,
    ( spl4_3
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f999,plain,
    ( spl4_93
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1114,plain,
    ( spl4_104
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f1144,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) )
    | ~ spl4_3
    | ~ spl4_93
    | ~ spl4_104 ),
    inference(backward_demodulation,[],[f1000,f1121])).

fof(f1121,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_3
    | ~ spl4_104 ),
    inference(resolution,[],[f1115,f114])).

fof(f114,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1115,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_104 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f1000,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0))) )
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f999])).

fof(f1149,plain,
    ( spl4_108
    | ~ spl4_3
    | ~ spl4_104 ),
    inference(avatar_split_clause,[],[f1121,f1114,f112,f1146])).

fof(f1116,plain,
    ( spl4_104
    | ~ spl4_10
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f1109,f346,f150,f1114])).

fof(f150,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f346,plain,
    ( spl4_31
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1109,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_10
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f190,f348])).

fof(f348,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f346])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_10 ),
    inference(resolution,[],[f68,f152])).

fof(f152,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1001,plain,
    ( spl4_93
    | ~ spl4_14
    | ~ spl4_69 ),
    inference(avatar_split_clause,[],[f797,f791,f200,f999])).

fof(f791,plain,
    ( spl4_69
  <=> v1_funct_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f797,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0))) )
    | ~ spl4_14
    | ~ spl4_69 ),
    inference(subsumption_resolution,[],[f795,f201])).

fof(f795,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0)))
        | ~ v1_relat_1(k7_relat_1(sK3,sK2)) )
    | ~ spl4_69 ),
    inference(resolution,[],[f793,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f793,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f791])).

fof(f981,plain,
    ( ~ spl4_71
    | spl4_27
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f978,f683,f317,f804])).

fof(f317,plain,
    ( spl4_27
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f683,plain,
    ( spl4_59
  <=> ! [X3] : k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f978,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_27
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f319,f684])).

fof(f684,plain,
    ( ! [X3] : k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f683])).

fof(f319,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f317])).

fof(f892,plain,
    ( spl4_82
    | ~ spl4_78 ),
    inference(avatar_split_clause,[],[f872,f862,f890])).

fof(f862,plain,
    ( spl4_78
  <=> ! [X3] : m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f872,plain,
    ( ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1)
    | ~ spl4_78 ),
    inference(resolution,[],[f863,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f863,plain,
    ( ! [X3] : m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_78 ),
    inference(avatar_component_clause,[],[f862])).

fof(f864,plain,
    ( spl4_78
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f856,f683,f133,f102,f862])).

fof(f102,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f133,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f856,plain,
    ( ! [X3] : m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f257,f684])).

fof(f257,plain,
    ( ! [X3] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f255,f104])).

fof(f104,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f255,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f93,f135])).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f817,plain,
    ( ~ spl4_73
    | ~ spl4_1
    | ~ spl4_7
    | spl4_28 ),
    inference(avatar_split_clause,[],[f777,f321,f133,f102,f814])).

fof(f321,plain,
    ( spl4_28
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f777,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | spl4_28 ),
    inference(backward_demodulation,[],[f323,f620])).

fof(f620,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f616,f104])).

fof(f616,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f135,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f323,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f321])).

fof(f794,plain,
    ( spl4_69
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f779,f313,f133,f102,f791])).

fof(f313,plain,
    ( spl4_26
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f779,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f314,f620])).

fof(f314,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f313])).

fof(f785,plain,
    ( spl4_59
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f620,f133,f102,f683])).

fof(f721,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | spl4_62 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | spl4_62 ),
    inference(subsumption_resolution,[],[f719,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f719,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | spl4_62 ),
    inference(forward_demodulation,[],[f716,f213])).

fof(f213,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl4_15
  <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f716,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_1
    | ~ spl4_7
    | spl4_62 ),
    inference(backward_demodulation,[],[f709,f310])).

fof(f310,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f306,f104])).

fof(f306,plain,
    ( ! [X0] :
        ( k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f135,f91])).

fof(f709,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl4_62 ),
    inference(avatar_component_clause,[],[f707])).

fof(f707,plain,
    ( spl4_62
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f710,plain,
    ( ~ spl4_62
    | spl4_28
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f690,f522,f321,f707])).

fof(f522,plain,
    ( spl4_47
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f690,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl4_28
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f323,f524])).

fof(f524,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f522])).

fof(f688,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | ~ spl4_30
    | spl4_57 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | ~ spl4_30
    | spl4_57 ),
    inference(subsumption_resolution,[],[f686,f342])).

fof(f342,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl4_30
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f686,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | spl4_57 ),
    inference(forward_demodulation,[],[f680,f213])).

fof(f680,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_1
    | ~ spl4_7
    | spl4_57 ),
    inference(backward_demodulation,[],[f653,f244])).

fof(f244,plain,
    ( ! [X3] : k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f242,f104])).

fof(f242,plain,
    ( ! [X3] :
        ( k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3)
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f91,f135])).

fof(f653,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_57 ),
    inference(avatar_component_clause,[],[f651])).

fof(f651,plain,
    ( spl4_57
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f654,plain,
    ( ~ spl4_57
    | spl4_27
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f600,f522,f317,f651])).

fof(f600,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_27
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f319,f524])).

fof(f525,plain,
    ( spl4_47
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f514,f501,f142,f112,f522])).

fof(f142,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f501,plain,
    ( spl4_46
  <=> ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f514,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f513,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f513,plain,
    ( sK0 = sK2
    | ~ spl4_3
    | ~ spl4_9
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f512,f502])).

fof(f502,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f501])).

fof(f512,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK0 = sK2
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f300,f144])).

fof(f300,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_3 ),
    inference(resolution,[],[f114,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f503,plain,
    ( spl4_46
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f496,f161,f127,f501])).

fof(f127,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f161,plain,
    ( spl4_11
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f496,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f173,f182])).

fof(f182,plain,(
    ! [X0] : v5_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f83,f63])).

fof(f173,plain,
    ( ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ v5_relat_1(k1_xboole_0,X1) )
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f168,f129])).

fof(f129,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f168,plain,
    ( ! [X1] :
        ( ~ v5_relat_1(k1_xboole_0,X1)
        | r1_tarski(k2_relat_1(k1_xboole_0),X1) )
    | ~ spl4_11 ),
    inference(resolution,[],[f163,f69])).

fof(f163,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f349,plain,
    ( spl4_31
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f344,f263,f133,f346])).

fof(f263,plain,
    ( spl4_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f344,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_7
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f197,f265])).

fof(f265,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f263])).

fof(f197,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f81,f135])).

fof(f343,plain,
    ( spl4_30
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f338,f332,f341])).

fof(f332,plain,
    ( spl4_29
  <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f338,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f337,f63])).

fof(f337,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl4_29 ),
    inference(trivial_inequality_removal,[],[f335])).

fof(f335,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl4_29 ),
    inference(superposition,[],[f99,f333])).

fof(f333,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f332])).

fof(f99,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f334,plain,
    ( spl4_29
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f198,f122,f332])).

fof(f122,plain,
    ( spl4_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f198,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f196,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f196,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f81,f63])).

fof(f326,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | spl4_26 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_7
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f104,f135,f315,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f315,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f313])).

fof(f324,plain,
    ( ~ spl4_26
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f59,f321,f317,f313])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f266,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f261,f138,f133,f117,f263])).

fof(f117,plain,
    ( spl4_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f261,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8 ),
    inference(subsumption_resolution,[],[f260,f140])).

fof(f260,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f259,f119])).

fof(f119,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f259,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f84,f135])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f214,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f157,f150,f211])).

fof(f157,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_10 ),
    inference(resolution,[],[f152,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f202,plain,
    ( spl4_14
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f158,f150,f102,f200])).

fof(f158,plain,
    ( ! [X2] : v1_relat_1(k7_relat_1(sK3,X2))
    | ~ spl4_1
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f156,f104])).

fof(f156,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | v1_relat_1(k7_relat_1(sK3,X2)) )
    | ~ spl4_10 ),
    inference(resolution,[],[f152,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f164,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f147,f161])).

fof(f147,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f80,f63])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f153,plain,
    ( spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f148,f133,f150])).

fof(f148,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f80,f135])).

fof(f145,plain,
    ( ~ spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f58,f142,f138])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f136,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f133])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f62,f127])).

fof(f62,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f125,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f61,f122])).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f120,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f55,f117])).

fof(f55,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f115,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f57,f112])).

fof(f57,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f54,f102])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:51:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (16420)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (16427)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (16434)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (16417)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (16416)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (16437)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (16418)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (16424)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (16429)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (16425)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (16438)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (16430)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (16415)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (16426)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (16421)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (16422)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (16419)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (16435)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (16440)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (16436)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (16432)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.56  % (16428)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (16423)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (16431)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.51/0.57  % (16433)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.51/0.58  % (16439)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.51/0.59  % (16417)Refutation found. Thanks to Tanya!
% 1.51/0.59  % SZS status Theorem for theBenchmark
% 1.51/0.59  % SZS output start Proof for theBenchmark
% 1.51/0.59  fof(f1558,plain,(
% 1.51/0.59    $false),
% 1.51/0.59    inference(avatar_sat_refutation,[],[f105,f115,f120,f125,f130,f136,f145,f153,f164,f202,f214,f266,f324,f326,f334,f343,f349,f503,f525,f654,f688,f710,f721,f785,f794,f817,f864,f892,f981,f1001,f1116,f1149,f1153,f1484,f1520,f1531,f1549,f1557])).
% 1.51/0.59  fof(f1557,plain,(
% 1.51/0.59    spl4_8 | spl4_71 | ~spl4_73 | ~spl4_144),
% 1.51/0.59    inference(avatar_contradiction_clause,[],[f1556])).
% 1.51/0.59  fof(f1556,plain,(
% 1.51/0.59    $false | (spl4_8 | spl4_71 | ~spl4_73 | ~spl4_144)),
% 1.51/0.59    inference(subsumption_resolution,[],[f1555,f815])).
% 1.51/0.59  fof(f815,plain,(
% 1.51/0.59    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_73),
% 1.51/0.59    inference(avatar_component_clause,[],[f814])).
% 1.51/0.59  fof(f814,plain,(
% 1.51/0.59    spl4_73 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 1.51/0.59  fof(f1555,plain,(
% 1.51/0.59    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_8 | spl4_71 | ~spl4_144)),
% 1.51/0.59    inference(subsumption_resolution,[],[f1554,f140])).
% 1.51/0.59  fof(f140,plain,(
% 1.51/0.59    k1_xboole_0 != sK1 | spl4_8),
% 1.51/0.59    inference(avatar_component_clause,[],[f138])).
% 1.51/0.59  fof(f138,plain,(
% 1.51/0.59    spl4_8 <=> k1_xboole_0 = sK1),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.51/0.59  fof(f1554,plain,(
% 1.51/0.59    k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_71 | ~spl4_144)),
% 1.51/0.59    inference(subsumption_resolution,[],[f1552,f805])).
% 1.51/0.59  fof(f805,plain,(
% 1.51/0.59    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_71),
% 1.51/0.59    inference(avatar_component_clause,[],[f804])).
% 1.51/0.59  fof(f804,plain,(
% 1.51/0.59    spl4_71 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.51/0.59  fof(f1552,plain,(
% 1.51/0.59    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_144),
% 1.51/0.59    inference(trivial_inequality_removal,[],[f1551])).
% 1.51/0.59  fof(f1551,plain,(
% 1.51/0.59    sK2 != sK2 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_144),
% 1.51/0.59    inference(superposition,[],[f86,f1548])).
% 1.51/0.59  fof(f1548,plain,(
% 1.51/0.59    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_144),
% 1.51/0.59    inference(avatar_component_clause,[],[f1546])).
% 1.51/0.59  fof(f1546,plain,(
% 1.51/0.59    spl4_144 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).
% 1.51/0.59  fof(f86,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.59    inference(cnf_transformation,[],[f53])).
% 1.51/0.59  fof(f53,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.59    inference(nnf_transformation,[],[f41])).
% 1.51/0.59  fof(f41,plain,(
% 1.51/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.59    inference(flattening,[],[f40])).
% 1.51/0.59  fof(f40,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.59    inference(ennf_transformation,[],[f17])).
% 1.51/0.59  fof(f17,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.51/0.59  fof(f1549,plain,(
% 1.51/0.59    spl4_144 | ~spl4_73 | ~spl4_108),
% 1.51/0.59    inference(avatar_split_clause,[],[f1542,f1146,f814,f1546])).
% 1.51/0.59  fof(f1146,plain,(
% 1.51/0.59    spl4_108 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).
% 1.51/0.59  fof(f1542,plain,(
% 1.51/0.59    sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | (~spl4_73 | ~spl4_108)),
% 1.51/0.59    inference(forward_demodulation,[],[f1536,f1148])).
% 1.51/0.59  fof(f1148,plain,(
% 1.51/0.59    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_108),
% 1.51/0.59    inference(avatar_component_clause,[],[f1146])).
% 1.51/0.59  fof(f1536,plain,(
% 1.51/0.59    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_73),
% 1.51/0.59    inference(resolution,[],[f815,f81])).
% 1.51/0.59  fof(f81,plain,(
% 1.51/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.51/0.59    inference(cnf_transformation,[],[f38])).
% 1.51/0.59  fof(f38,plain,(
% 1.51/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.59    inference(ennf_transformation,[],[f16])).
% 1.51/0.59  fof(f16,axiom,(
% 1.51/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.51/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.51/0.59  fof(f1531,plain,(
% 1.51/0.59    spl4_73 | ~spl4_109 | ~spl4_143),
% 1.51/0.59    inference(avatar_contradiction_clause,[],[f1530])).
% 1.51/0.59  fof(f1530,plain,(
% 1.51/0.59    $false | (spl4_73 | ~spl4_109 | ~spl4_143)),
% 1.51/0.59    inference(subsumption_resolution,[],[f1524,f816])).
% 1.51/0.59  fof(f816,plain,(
% 1.51/0.59    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_73),
% 1.51/0.59    inference(avatar_component_clause,[],[f814])).
% 1.51/0.59  fof(f1524,plain,(
% 1.51/0.59    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_109 | ~spl4_143)),
% 1.51/0.59    inference(resolution,[],[f1519,f1152])).
% 1.51/0.59  fof(f1152,plain,(
% 1.51/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl4_109),
% 1.51/0.59    inference(avatar_component_clause,[],[f1151])).
% 1.51/0.59  fof(f1151,plain,(
% 1.51/0.59    spl4_109 <=> ! [X0] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).
% 1.51/0.59  fof(f1519,plain,(
% 1.51/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | ~spl4_143),
% 1.51/0.59    inference(avatar_component_clause,[],[f1518])).
% 1.51/0.59  fof(f1518,plain,(
% 1.51/0.59    spl4_143 <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).
% 1.51/0.59  fof(f1520,plain,(
% 1.51/0.59    spl4_143 | ~spl4_82 | ~spl4_138),
% 1.51/0.59    inference(avatar_split_clause,[],[f1503,f1464,f890,f1518])).
% 1.51/0.59  fof(f890,plain,(
% 1.51/0.59    spl4_82 <=> ! [X3] : v5_relat_1(k7_relat_1(sK3,X3),sK1)),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 1.51/0.59  fof(f1464,plain,(
% 1.51/0.59    spl4_138 <=> ! [X5,X4] : (~v5_relat_1(k7_relat_1(sK3,X4),X5) | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).
% 1.51/0.59  fof(f1503,plain,(
% 1.51/0.59    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_82 | ~spl4_138)),
% 1.51/0.59    inference(resolution,[],[f1465,f891])).
% 1.51/0.59  fof(f891,plain,(
% 1.51/0.59    ( ! [X3] : (v5_relat_1(k7_relat_1(sK3,X3),sK1)) ) | ~spl4_82),
% 1.51/0.59    inference(avatar_component_clause,[],[f890])).
% 1.51/0.59  fof(f1465,plain,(
% 1.51/0.59    ( ! [X4,X5] : (~v5_relat_1(k7_relat_1(sK3,X4),X5) | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5)) ) | ~spl4_138),
% 1.51/0.59    inference(avatar_component_clause,[],[f1464])).
% 1.51/0.59  fof(f1484,plain,(
% 1.51/0.59    spl4_138 | ~spl4_14),
% 1.51/0.59    inference(avatar_split_clause,[],[f657,f200,f1464])).
% 1.51/0.59  fof(f200,plain,(
% 1.51/0.59    spl4_14 <=> ! [X2] : v1_relat_1(k7_relat_1(sK3,X2))),
% 1.51/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.51/0.59  fof(f657,plain,(
% 1.51/0.59    ( ! [X4,X5] : (~v5_relat_1(k7_relat_1(sK3,X4),X5) | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),X5)) ) | ~spl4_14),
% 1.51/0.59    inference(resolution,[],[f201,f69])).
% 1.75/0.59  fof(f69,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f50])).
% 1.75/0.59  fof(f50,plain,(
% 1.75/0.59    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(nnf_transformation,[],[f31])).
% 1.75/0.59  fof(f31,plain,(
% 1.75/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f7])).
% 1.75/0.59  fof(f7,axiom,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.75/0.59  fof(f201,plain,(
% 1.75/0.59    ( ! [X2] : (v1_relat_1(k7_relat_1(sK3,X2))) ) | ~spl4_14),
% 1.75/0.59    inference(avatar_component_clause,[],[f200])).
% 1.75/0.59  fof(f1153,plain,(
% 1.75/0.59    spl4_109 | ~spl4_3 | ~spl4_93 | ~spl4_104),
% 1.75/0.59    inference(avatar_split_clause,[],[f1144,f1114,f999,f112,f1151])).
% 1.75/0.59  fof(f112,plain,(
% 1.75/0.59    spl4_3 <=> r1_tarski(sK2,sK0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.75/0.59  fof(f999,plain,(
% 1.75/0.59    spl4_93 <=> ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0))))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 1.75/0.59  fof(f1114,plain,(
% 1.75/0.59    spl4_104 <=> ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).
% 1.75/0.59  fof(f1144,plain,(
% 1.75/0.59    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0)) ) | (~spl4_3 | ~spl4_93 | ~spl4_104)),
% 1.75/0.59    inference(backward_demodulation,[],[f1000,f1121])).
% 1.75/0.59  fof(f1121,plain,(
% 1.75/0.59    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_3 | ~spl4_104)),
% 1.75/0.59    inference(resolution,[],[f1115,f114])).
% 1.75/0.59  fof(f114,plain,(
% 1.75/0.59    r1_tarski(sK2,sK0) | ~spl4_3),
% 1.75/0.59    inference(avatar_component_clause,[],[f112])).
% 1.75/0.59  fof(f1115,plain,(
% 1.75/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_104),
% 1.75/0.59    inference(avatar_component_clause,[],[f1114])).
% 1.75/0.59  fof(f1000,plain,(
% 1.75/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0)))) ) | ~spl4_93),
% 1.75/0.59    inference(avatar_component_clause,[],[f999])).
% 1.75/0.59  fof(f1149,plain,(
% 1.75/0.59    spl4_108 | ~spl4_3 | ~spl4_104),
% 1.75/0.59    inference(avatar_split_clause,[],[f1121,f1114,f112,f1146])).
% 1.75/0.59  fof(f1116,plain,(
% 1.75/0.59    spl4_104 | ~spl4_10 | ~spl4_31),
% 1.75/0.59    inference(avatar_split_clause,[],[f1109,f346,f150,f1114])).
% 1.75/0.59  fof(f150,plain,(
% 1.75/0.59    spl4_10 <=> v1_relat_1(sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.75/0.59  fof(f346,plain,(
% 1.75/0.59    spl4_31 <=> sK0 = k1_relat_1(sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.75/0.59  fof(f1109,plain,(
% 1.75/0.59    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_10 | ~spl4_31)),
% 1.75/0.59    inference(forward_demodulation,[],[f190,f348])).
% 1.75/0.59  fof(f348,plain,(
% 1.75/0.59    sK0 = k1_relat_1(sK3) | ~spl4_31),
% 1.75/0.59    inference(avatar_component_clause,[],[f346])).
% 1.75/0.59  fof(f190,plain,(
% 1.75/0.59    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_10),
% 1.75/0.59    inference(resolution,[],[f68,f152])).
% 1.75/0.59  fof(f152,plain,(
% 1.75/0.59    v1_relat_1(sK3) | ~spl4_10),
% 1.75/0.59    inference(avatar_component_clause,[],[f150])).
% 1.75/0.59  fof(f68,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.75/0.59    inference(cnf_transformation,[],[f30])).
% 1.75/0.59  fof(f30,plain,(
% 1.75/0.59    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(flattening,[],[f29])).
% 1.75/0.59  fof(f29,plain,(
% 1.75/0.59    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f10])).
% 1.75/0.59  fof(f10,axiom,(
% 1.75/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.75/0.59  fof(f1001,plain,(
% 1.75/0.59    spl4_93 | ~spl4_14 | ~spl4_69),
% 1.75/0.59    inference(avatar_split_clause,[],[f797,f791,f200,f999])).
% 1.75/0.59  fof(f791,plain,(
% 1.75/0.59    spl4_69 <=> v1_funct_1(k7_relat_1(sK3,sK2))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.75/0.59  fof(f797,plain,(
% 1.75/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0)))) ) | (~spl4_14 | ~spl4_69)),
% 1.75/0.59    inference(subsumption_resolution,[],[f795,f201])).
% 1.75/0.59  fof(f795,plain,(
% 1.75/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X0))) | ~v1_relat_1(k7_relat_1(sK3,sK2))) ) | ~spl4_69),
% 1.75/0.59    inference(resolution,[],[f793,f75])).
% 1.75/0.59  fof(f75,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f35])).
% 1.75/0.59  fof(f35,plain,(
% 1.75/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.75/0.59    inference(flattening,[],[f34])).
% 1.75/0.59  fof(f34,plain,(
% 1.75/0.59    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.75/0.59    inference(ennf_transformation,[],[f20])).
% 1.75/0.59  fof(f20,axiom,(
% 1.75/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.75/0.59  fof(f793,plain,(
% 1.75/0.59    v1_funct_1(k7_relat_1(sK3,sK2)) | ~spl4_69),
% 1.75/0.59    inference(avatar_component_clause,[],[f791])).
% 1.75/0.59  fof(f981,plain,(
% 1.75/0.59    ~spl4_71 | spl4_27 | ~spl4_59),
% 1.75/0.59    inference(avatar_split_clause,[],[f978,f683,f317,f804])).
% 1.75/0.59  fof(f317,plain,(
% 1.75/0.59    spl4_27 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.75/0.59  fof(f683,plain,(
% 1.75/0.59    spl4_59 <=> ! [X3] : k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.75/0.59  fof(f978,plain,(
% 1.75/0.59    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_27 | ~spl4_59)),
% 1.75/0.59    inference(forward_demodulation,[],[f319,f684])).
% 1.75/0.59  fof(f684,plain,(
% 1.75/0.59    ( ! [X3] : (k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3)) ) | ~spl4_59),
% 1.75/0.59    inference(avatar_component_clause,[],[f683])).
% 1.75/0.59  fof(f319,plain,(
% 1.75/0.59    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_27),
% 1.75/0.59    inference(avatar_component_clause,[],[f317])).
% 1.75/0.59  fof(f892,plain,(
% 1.75/0.59    spl4_82 | ~spl4_78),
% 1.75/0.59    inference(avatar_split_clause,[],[f872,f862,f890])).
% 1.75/0.59  fof(f862,plain,(
% 1.75/0.59    spl4_78 <=> ! [X3] : m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 1.75/0.59  fof(f872,plain,(
% 1.75/0.59    ( ! [X3] : (v5_relat_1(k7_relat_1(sK3,X3),sK1)) ) | ~spl4_78),
% 1.75/0.59    inference(resolution,[],[f863,f83])).
% 1.75/0.59  fof(f83,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f39])).
% 1.75/0.59  fof(f39,plain,(
% 1.75/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.59    inference(ennf_transformation,[],[f14])).
% 1.75/0.59  fof(f14,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.75/0.59  fof(f863,plain,(
% 1.75/0.59    ( ! [X3] : (m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_78),
% 1.75/0.59    inference(avatar_component_clause,[],[f862])).
% 1.75/0.59  fof(f864,plain,(
% 1.75/0.59    spl4_78 | ~spl4_1 | ~spl4_7 | ~spl4_59),
% 1.75/0.59    inference(avatar_split_clause,[],[f856,f683,f133,f102,f862])).
% 1.75/0.59  fof(f102,plain,(
% 1.75/0.59    spl4_1 <=> v1_funct_1(sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.75/0.59  fof(f133,plain,(
% 1.75/0.59    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.75/0.59  fof(f856,plain,(
% 1.75/0.59    ( ! [X3] : (m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_7 | ~spl4_59)),
% 1.75/0.59    inference(forward_demodulation,[],[f257,f684])).
% 1.75/0.59  fof(f257,plain,(
% 1.75/0.59    ( ! [X3] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_1 | ~spl4_7)),
% 1.75/0.59    inference(subsumption_resolution,[],[f255,f104])).
% 1.75/0.59  fof(f104,plain,(
% 1.75/0.59    v1_funct_1(sK3) | ~spl4_1),
% 1.75/0.59    inference(avatar_component_clause,[],[f102])).
% 1.75/0.59  fof(f255,plain,(
% 1.75/0.59    ( ! [X3] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) ) | ~spl4_7),
% 1.75/0.59    inference(resolution,[],[f93,f135])).
% 1.75/0.59  fof(f135,plain,(
% 1.75/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 1.75/0.59    inference(avatar_component_clause,[],[f133])).
% 1.75/0.59  fof(f93,plain,(
% 1.75/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f47])).
% 1.75/0.59  fof(f47,plain,(
% 1.75/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.75/0.59    inference(flattening,[],[f46])).
% 1.75/0.59  fof(f46,plain,(
% 1.75/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.75/0.59    inference(ennf_transformation,[],[f18])).
% 1.75/0.59  fof(f18,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.75/0.59  fof(f817,plain,(
% 1.75/0.59    ~spl4_73 | ~spl4_1 | ~spl4_7 | spl4_28),
% 1.75/0.59    inference(avatar_split_clause,[],[f777,f321,f133,f102,f814])).
% 1.75/0.59  fof(f321,plain,(
% 1.75/0.59    spl4_28 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.75/0.59  fof(f777,plain,(
% 1.75/0.59    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_1 | ~spl4_7 | spl4_28)),
% 1.75/0.59    inference(backward_demodulation,[],[f323,f620])).
% 1.75/0.59  fof(f620,plain,(
% 1.75/0.59    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | (~spl4_1 | ~spl4_7)),
% 1.75/0.59    inference(subsumption_resolution,[],[f616,f104])).
% 1.75/0.59  fof(f616,plain,(
% 1.75/0.59    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) | ~v1_funct_1(sK3)) ) | ~spl4_7),
% 1.75/0.59    inference(resolution,[],[f135,f91])).
% 1.75/0.59  fof(f91,plain,(
% 1.75/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f45])).
% 1.75/0.59  fof(f45,plain,(
% 1.75/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.75/0.59    inference(flattening,[],[f44])).
% 1.75/0.59  fof(f44,plain,(
% 1.75/0.59    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.75/0.59    inference(ennf_transformation,[],[f19])).
% 1.75/0.59  fof(f19,axiom,(
% 1.75/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.75/0.59  fof(f323,plain,(
% 1.75/0.59    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_28),
% 1.75/0.59    inference(avatar_component_clause,[],[f321])).
% 1.75/0.59  fof(f794,plain,(
% 1.75/0.59    spl4_69 | ~spl4_1 | ~spl4_7 | ~spl4_26),
% 1.75/0.59    inference(avatar_split_clause,[],[f779,f313,f133,f102,f791])).
% 1.75/0.59  fof(f313,plain,(
% 1.75/0.59    spl4_26 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.75/0.59  fof(f779,plain,(
% 1.75/0.59    v1_funct_1(k7_relat_1(sK3,sK2)) | (~spl4_1 | ~spl4_7 | ~spl4_26)),
% 1.75/0.59    inference(backward_demodulation,[],[f314,f620])).
% 1.75/0.59  fof(f314,plain,(
% 1.75/0.59    v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_26),
% 1.75/0.59    inference(avatar_component_clause,[],[f313])).
% 1.75/0.59  fof(f785,plain,(
% 1.75/0.59    spl4_59 | ~spl4_1 | ~spl4_7),
% 1.75/0.59    inference(avatar_split_clause,[],[f620,f133,f102,f683])).
% 1.75/0.59  fof(f721,plain,(
% 1.75/0.59    ~spl4_1 | ~spl4_7 | ~spl4_15 | spl4_62),
% 1.75/0.59    inference(avatar_contradiction_clause,[],[f720])).
% 1.75/0.59  fof(f720,plain,(
% 1.75/0.59    $false | (~spl4_1 | ~spl4_7 | ~spl4_15 | spl4_62)),
% 1.75/0.59    inference(subsumption_resolution,[],[f719,f63])).
% 1.75/0.59  fof(f63,plain,(
% 1.75/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f5])).
% 1.75/0.59  fof(f5,axiom,(
% 1.75/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.75/0.59  fof(f719,plain,(
% 1.75/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_1 | ~spl4_7 | ~spl4_15 | spl4_62)),
% 1.75/0.59    inference(forward_demodulation,[],[f716,f213])).
% 1.75/0.59  fof(f213,plain,(
% 1.75/0.59    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_15),
% 1.75/0.59    inference(avatar_component_clause,[],[f211])).
% 1.75/0.59  fof(f211,plain,(
% 1.75/0.59    spl4_15 <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.75/0.59  fof(f716,plain,(
% 1.75/0.59    ~m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_1 | ~spl4_7 | spl4_62)),
% 1.75/0.59    inference(backward_demodulation,[],[f709,f310])).
% 1.75/0.59  fof(f310,plain,(
% 1.75/0.59    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | (~spl4_1 | ~spl4_7)),
% 1.75/0.59    inference(subsumption_resolution,[],[f306,f104])).
% 1.75/0.59  fof(f306,plain,(
% 1.75/0.59    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) | ~v1_funct_1(sK3)) ) | ~spl4_7),
% 1.75/0.59    inference(resolution,[],[f135,f91])).
% 1.75/0.59  fof(f709,plain,(
% 1.75/0.59    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | spl4_62),
% 1.75/0.59    inference(avatar_component_clause,[],[f707])).
% 1.75/0.59  fof(f707,plain,(
% 1.75/0.59    spl4_62 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 1.75/0.59  fof(f710,plain,(
% 1.75/0.59    ~spl4_62 | spl4_28 | ~spl4_47),
% 1.75/0.59    inference(avatar_split_clause,[],[f690,f522,f321,f707])).
% 1.75/0.59  fof(f522,plain,(
% 1.75/0.59    spl4_47 <=> k1_xboole_0 = sK2),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.75/0.59  fof(f690,plain,(
% 1.75/0.59    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (spl4_28 | ~spl4_47)),
% 1.75/0.59    inference(forward_demodulation,[],[f323,f524])).
% 1.75/0.59  fof(f524,plain,(
% 1.75/0.59    k1_xboole_0 = sK2 | ~spl4_47),
% 1.75/0.59    inference(avatar_component_clause,[],[f522])).
% 1.75/0.59  fof(f688,plain,(
% 1.75/0.59    ~spl4_1 | ~spl4_7 | ~spl4_15 | ~spl4_30 | spl4_57),
% 1.75/0.59    inference(avatar_contradiction_clause,[],[f687])).
% 1.75/0.59  fof(f687,plain,(
% 1.75/0.59    $false | (~spl4_1 | ~spl4_7 | ~spl4_15 | ~spl4_30 | spl4_57)),
% 1.75/0.59    inference(subsumption_resolution,[],[f686,f342])).
% 1.75/0.59  fof(f342,plain,(
% 1.75/0.59    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_30),
% 1.75/0.59    inference(avatar_component_clause,[],[f341])).
% 1.75/0.59  fof(f341,plain,(
% 1.75/0.59    spl4_30 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.75/0.59  fof(f686,plain,(
% 1.75/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl4_1 | ~spl4_7 | ~spl4_15 | spl4_57)),
% 1.75/0.59    inference(forward_demodulation,[],[f680,f213])).
% 1.75/0.59  fof(f680,plain,(
% 1.75/0.59    ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | (~spl4_1 | ~spl4_7 | spl4_57)),
% 1.75/0.59    inference(backward_demodulation,[],[f653,f244])).
% 1.75/0.59  fof(f244,plain,(
% 1.75/0.59    ( ! [X3] : (k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3)) ) | (~spl4_1 | ~spl4_7)),
% 1.75/0.59    inference(subsumption_resolution,[],[f242,f104])).
% 1.75/0.59  fof(f242,plain,(
% 1.75/0.59    ( ! [X3] : (k7_relat_1(sK3,X3) = k2_partfun1(sK0,sK1,sK3,X3) | ~v1_funct_1(sK3)) ) | ~spl4_7),
% 1.75/0.59    inference(resolution,[],[f91,f135])).
% 1.75/0.59  fof(f653,plain,(
% 1.75/0.59    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | spl4_57),
% 1.75/0.59    inference(avatar_component_clause,[],[f651])).
% 1.75/0.59  fof(f651,plain,(
% 1.75/0.59    spl4_57 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.75/0.59  fof(f654,plain,(
% 1.75/0.59    ~spl4_57 | spl4_27 | ~spl4_47),
% 1.75/0.59    inference(avatar_split_clause,[],[f600,f522,f317,f651])).
% 1.75/0.59  fof(f600,plain,(
% 1.75/0.59    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | (spl4_27 | ~spl4_47)),
% 1.75/0.59    inference(forward_demodulation,[],[f319,f524])).
% 1.75/0.59  fof(f525,plain,(
% 1.75/0.59    spl4_47 | ~spl4_3 | ~spl4_9 | ~spl4_46),
% 1.75/0.59    inference(avatar_split_clause,[],[f514,f501,f142,f112,f522])).
% 1.75/0.59  fof(f142,plain,(
% 1.75/0.59    spl4_9 <=> k1_xboole_0 = sK0),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.75/0.59  fof(f501,plain,(
% 1.75/0.59    spl4_46 <=> ! [X1] : r1_tarski(k1_xboole_0,X1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.75/0.59  fof(f514,plain,(
% 1.75/0.59    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_9 | ~spl4_46)),
% 1.75/0.59    inference(forward_demodulation,[],[f513,f144])).
% 1.75/0.59  fof(f144,plain,(
% 1.75/0.59    k1_xboole_0 = sK0 | ~spl4_9),
% 1.75/0.59    inference(avatar_component_clause,[],[f142])).
% 1.75/0.59  fof(f513,plain,(
% 1.75/0.59    sK0 = sK2 | (~spl4_3 | ~spl4_9 | ~spl4_46)),
% 1.75/0.59    inference(subsumption_resolution,[],[f512,f502])).
% 1.75/0.59  fof(f502,plain,(
% 1.75/0.59    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | ~spl4_46),
% 1.75/0.59    inference(avatar_component_clause,[],[f501])).
% 1.75/0.59  fof(f512,plain,(
% 1.75/0.59    ~r1_tarski(k1_xboole_0,sK2) | sK0 = sK2 | (~spl4_3 | ~spl4_9)),
% 1.75/0.59    inference(forward_demodulation,[],[f300,f144])).
% 1.75/0.59  fof(f300,plain,(
% 1.75/0.59    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_3),
% 1.75/0.59    inference(resolution,[],[f114,f78])).
% 1.75/0.59  fof(f78,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.75/0.59    inference(cnf_transformation,[],[f52])).
% 1.75/0.59  fof(f52,plain,(
% 1.75/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.59    inference(flattening,[],[f51])).
% 1.75/0.59  fof(f51,plain,(
% 1.75/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.75/0.59    inference(nnf_transformation,[],[f3])).
% 1.75/0.59  fof(f3,axiom,(
% 1.75/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.75/0.59  fof(f503,plain,(
% 1.75/0.59    spl4_46 | ~spl4_6 | ~spl4_11),
% 1.75/0.59    inference(avatar_split_clause,[],[f496,f161,f127,f501])).
% 1.75/0.59  fof(f127,plain,(
% 1.75/0.59    spl4_6 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.75/0.59  fof(f161,plain,(
% 1.75/0.59    spl4_11 <=> v1_relat_1(k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.75/0.59  fof(f496,plain,(
% 1.75/0.59    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | (~spl4_6 | ~spl4_11)),
% 1.75/0.59    inference(subsumption_resolution,[],[f173,f182])).
% 1.75/0.59  fof(f182,plain,(
% 1.75/0.59    ( ! [X0] : (v5_relat_1(k1_xboole_0,X0)) )),
% 1.75/0.59    inference(resolution,[],[f83,f63])).
% 1.75/0.59  fof(f173,plain,(
% 1.75/0.59    ( ! [X1] : (r1_tarski(k1_xboole_0,X1) | ~v5_relat_1(k1_xboole_0,X1)) ) | (~spl4_6 | ~spl4_11)),
% 1.75/0.59    inference(forward_demodulation,[],[f168,f129])).
% 1.75/0.59  fof(f129,plain,(
% 1.75/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_6),
% 1.75/0.59    inference(avatar_component_clause,[],[f127])).
% 1.75/0.59  fof(f168,plain,(
% 1.75/0.59    ( ! [X1] : (~v5_relat_1(k1_xboole_0,X1) | r1_tarski(k2_relat_1(k1_xboole_0),X1)) ) | ~spl4_11),
% 1.75/0.59    inference(resolution,[],[f163,f69])).
% 1.75/0.59  fof(f163,plain,(
% 1.75/0.59    v1_relat_1(k1_xboole_0) | ~spl4_11),
% 1.75/0.59    inference(avatar_component_clause,[],[f161])).
% 1.75/0.59  fof(f349,plain,(
% 1.75/0.59    spl4_31 | ~spl4_7 | ~spl4_20),
% 1.75/0.59    inference(avatar_split_clause,[],[f344,f263,f133,f346])).
% 1.75/0.59  fof(f263,plain,(
% 1.75/0.59    spl4_20 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.75/0.59  fof(f344,plain,(
% 1.75/0.59    sK0 = k1_relat_1(sK3) | (~spl4_7 | ~spl4_20)),
% 1.75/0.59    inference(forward_demodulation,[],[f197,f265])).
% 1.75/0.59  fof(f265,plain,(
% 1.75/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_20),
% 1.75/0.59    inference(avatar_component_clause,[],[f263])).
% 1.75/0.59  fof(f197,plain,(
% 1.75/0.59    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_7),
% 1.75/0.59    inference(resolution,[],[f81,f135])).
% 1.75/0.59  fof(f343,plain,(
% 1.75/0.59    spl4_30 | ~spl4_29),
% 1.75/0.59    inference(avatar_split_clause,[],[f338,f332,f341])).
% 1.75/0.59  fof(f332,plain,(
% 1.75/0.59    spl4_29 <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.75/0.59  fof(f338,plain,(
% 1.75/0.59    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_29),
% 1.75/0.59    inference(subsumption_resolution,[],[f337,f63])).
% 1.75/0.59  fof(f337,plain,(
% 1.75/0.59    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl4_29),
% 1.75/0.59    inference(trivial_inequality_removal,[],[f335])).
% 1.75/0.59  fof(f335,plain,(
% 1.75/0.59    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl4_29),
% 1.75/0.59    inference(superposition,[],[f99,f333])).
% 1.75/0.59  fof(f333,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_29),
% 1.75/0.59    inference(avatar_component_clause,[],[f332])).
% 1.75/0.59  fof(f99,plain,(
% 1.75/0.59    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.75/0.59    inference(equality_resolution,[],[f87])).
% 1.75/0.59  fof(f87,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f53])).
% 1.75/0.59  fof(f334,plain,(
% 1.75/0.59    spl4_29 | ~spl4_5),
% 1.75/0.59    inference(avatar_split_clause,[],[f198,f122,f332])).
% 1.75/0.59  fof(f122,plain,(
% 1.75/0.59    spl4_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.75/0.59  fof(f198,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_5),
% 1.75/0.59    inference(forward_demodulation,[],[f196,f124])).
% 1.75/0.59  fof(f124,plain,(
% 1.75/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_5),
% 1.75/0.59    inference(avatar_component_clause,[],[f122])).
% 1.75/0.59  fof(f196,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.75/0.59    inference(resolution,[],[f81,f63])).
% 1.75/0.59  fof(f326,plain,(
% 1.75/0.59    ~spl4_1 | ~spl4_7 | spl4_26),
% 1.75/0.59    inference(avatar_contradiction_clause,[],[f325])).
% 1.75/0.59  fof(f325,plain,(
% 1.75/0.59    $false | (~spl4_1 | ~spl4_7 | spl4_26)),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f104,f135,f315,f92])).
% 1.75/0.59  fof(f92,plain,(
% 1.75/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f47])).
% 1.75/0.59  fof(f315,plain,(
% 1.75/0.59    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_26),
% 1.75/0.59    inference(avatar_component_clause,[],[f313])).
% 1.75/0.59  fof(f324,plain,(
% 1.75/0.59    ~spl4_26 | ~spl4_27 | ~spl4_28),
% 1.75/0.59    inference(avatar_split_clause,[],[f59,f321,f317,f313])).
% 1.75/0.59  fof(f59,plain,(
% 1.75/0.59    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.75/0.59    inference(cnf_transformation,[],[f49])).
% 1.75/0.59  fof(f49,plain,(
% 1.75/0.59    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f48])).
% 1.75/0.59  fof(f48,plain,(
% 1.75/0.59    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f24,plain,(
% 1.75/0.59    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.75/0.59    inference(flattening,[],[f23])).
% 1.75/0.59  fof(f23,plain,(
% 1.75/0.59    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.75/0.59    inference(ennf_transformation,[],[f22])).
% 1.75/0.59  fof(f22,negated_conjecture,(
% 1.75/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.75/0.59    inference(negated_conjecture,[],[f21])).
% 1.75/0.59  fof(f21,conjecture,(
% 1.75/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.75/0.59  fof(f266,plain,(
% 1.75/0.59    spl4_20 | ~spl4_4 | ~spl4_7 | spl4_8),
% 1.75/0.59    inference(avatar_split_clause,[],[f261,f138,f133,f117,f263])).
% 1.75/0.59  fof(f117,plain,(
% 1.75/0.59    spl4_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.75/0.59  fof(f261,plain,(
% 1.75/0.59    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_4 | ~spl4_7 | spl4_8)),
% 1.75/0.59    inference(subsumption_resolution,[],[f260,f140])).
% 1.75/0.59  fof(f260,plain,(
% 1.75/0.59    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_4 | ~spl4_7)),
% 1.75/0.59    inference(subsumption_resolution,[],[f259,f119])).
% 1.75/0.59  fof(f119,plain,(
% 1.75/0.59    v1_funct_2(sK3,sK0,sK1) | ~spl4_4),
% 1.75/0.59    inference(avatar_component_clause,[],[f117])).
% 1.75/0.59  fof(f259,plain,(
% 1.75/0.59    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_7),
% 1.75/0.59    inference(resolution,[],[f84,f135])).
% 1.75/0.59  fof(f84,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.75/0.59    inference(cnf_transformation,[],[f53])).
% 1.75/0.59  fof(f214,plain,(
% 1.75/0.59    spl4_15 | ~spl4_10),
% 1.75/0.59    inference(avatar_split_clause,[],[f157,f150,f211])).
% 1.75/0.59  fof(f157,plain,(
% 1.75/0.59    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_10),
% 1.75/0.59    inference(resolution,[],[f152,f65])).
% 1.75/0.59  fof(f65,plain,(
% 1.75/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f26])).
% 1.75/0.59  fof(f26,plain,(
% 1.75/0.59    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f8])).
% 1.75/0.59  fof(f8,axiom,(
% 1.75/0.59    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 1.75/0.59  fof(f202,plain,(
% 1.75/0.59    spl4_14 | ~spl4_1 | ~spl4_10),
% 1.75/0.59    inference(avatar_split_clause,[],[f158,f150,f102,f200])).
% 1.75/0.59  fof(f158,plain,(
% 1.75/0.59    ( ! [X2] : (v1_relat_1(k7_relat_1(sK3,X2))) ) | (~spl4_1 | ~spl4_10)),
% 1.75/0.59    inference(subsumption_resolution,[],[f156,f104])).
% 1.75/0.59  fof(f156,plain,(
% 1.75/0.59    ( ! [X2] : (~v1_funct_1(sK3) | v1_relat_1(k7_relat_1(sK3,X2))) ) | ~spl4_10),
% 1.75/0.59    inference(resolution,[],[f152,f71])).
% 1.75/0.59  fof(f71,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f33])).
% 1.75/0.59  fof(f33,plain,(
% 1.75/0.59    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.59    inference(flattening,[],[f32])).
% 1.75/0.59  fof(f32,plain,(
% 1.75/0.59    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f12])).
% 1.75/0.59  fof(f12,axiom,(
% 1.75/0.59    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 1.75/0.59  fof(f164,plain,(
% 1.75/0.59    spl4_11),
% 1.75/0.59    inference(avatar_split_clause,[],[f147,f161])).
% 1.75/0.59  fof(f147,plain,(
% 1.75/0.59    v1_relat_1(k1_xboole_0)),
% 1.75/0.59    inference(resolution,[],[f80,f63])).
% 1.75/0.59  fof(f80,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f37])).
% 1.75/0.59  fof(f37,plain,(
% 1.75/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.59    inference(ennf_transformation,[],[f13])).
% 1.75/0.59  fof(f13,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.75/0.59  fof(f153,plain,(
% 1.75/0.59    spl4_10 | ~spl4_7),
% 1.75/0.59    inference(avatar_split_clause,[],[f148,f133,f150])).
% 1.75/0.59  fof(f148,plain,(
% 1.75/0.59    v1_relat_1(sK3) | ~spl4_7),
% 1.75/0.59    inference(resolution,[],[f80,f135])).
% 1.75/0.59  fof(f145,plain,(
% 1.75/0.59    ~spl4_8 | spl4_9),
% 1.75/0.59    inference(avatar_split_clause,[],[f58,f142,f138])).
% 1.75/0.59  fof(f58,plain,(
% 1.75/0.59    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.75/0.59    inference(cnf_transformation,[],[f49])).
% 1.75/0.59  fof(f136,plain,(
% 1.75/0.59    spl4_7),
% 1.75/0.59    inference(avatar_split_clause,[],[f56,f133])).
% 1.75/0.59  fof(f56,plain,(
% 1.75/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.59    inference(cnf_transformation,[],[f49])).
% 1.75/0.59  fof(f130,plain,(
% 1.75/0.59    spl4_6),
% 1.75/0.59    inference(avatar_split_clause,[],[f62,f127])).
% 1.75/0.59  fof(f62,plain,(
% 1.75/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.75/0.59    inference(cnf_transformation,[],[f9])).
% 1.75/0.59  fof(f9,axiom,(
% 1.75/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.75/0.59  fof(f125,plain,(
% 1.75/0.59    spl4_5),
% 1.75/0.59    inference(avatar_split_clause,[],[f61,f122])).
% 1.75/0.59  fof(f61,plain,(
% 1.75/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.75/0.59    inference(cnf_transformation,[],[f9])).
% 1.75/0.59  fof(f120,plain,(
% 1.75/0.59    spl4_4),
% 1.75/0.59    inference(avatar_split_clause,[],[f55,f117])).
% 1.75/0.59  fof(f55,plain,(
% 1.75/0.59    v1_funct_2(sK3,sK0,sK1)),
% 1.75/0.59    inference(cnf_transformation,[],[f49])).
% 1.75/0.59  fof(f115,plain,(
% 1.75/0.59    spl4_3),
% 1.75/0.59    inference(avatar_split_clause,[],[f57,f112])).
% 1.75/0.59  fof(f57,plain,(
% 1.75/0.59    r1_tarski(sK2,sK0)),
% 1.75/0.59    inference(cnf_transformation,[],[f49])).
% 1.75/0.59  fof(f105,plain,(
% 1.75/0.59    spl4_1),
% 1.75/0.59    inference(avatar_split_clause,[],[f54,f102])).
% 1.75/0.59  fof(f54,plain,(
% 1.75/0.59    v1_funct_1(sK3)),
% 1.75/0.59    inference(cnf_transformation,[],[f49])).
% 1.75/0.59  % SZS output end Proof for theBenchmark
% 1.75/0.59  % (16417)------------------------------
% 1.75/0.59  % (16417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (16417)Termination reason: Refutation
% 1.75/0.59  
% 1.75/0.59  % (16417)Memory used [KB]: 7164
% 1.75/0.59  % (16417)Time elapsed: 0.176 s
% 1.75/0.59  % (16417)------------------------------
% 1.75/0.59  % (16417)------------------------------
% 1.75/0.59  % (16414)Success in time 0.225 s
%------------------------------------------------------------------------------
