%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:25 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  284 ( 554 expanded)
%              Number of leaves         :   69 ( 239 expanded)
%              Depth                    :   12
%              Number of atoms          :  973 (1787 expanded)
%              Number of equality atoms :   95 ( 235 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1901,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f176,f181,f188,f200,f205,f212,f217,f223,f229,f237,f259,f319,f324,f480,f655,f738,f755,f891,f952,f959,f964,f1052,f1085,f1369,f1404,f1405,f1483,f1559,f1807,f1813,f1835,f1858,f1899])).

fof(f1899,plain,(
    spl9_136 ),
    inference(avatar_contradiction_clause,[],[f1895])).

fof(f1895,plain,
    ( $false
    | spl9_136 ),
    inference(unit_resulting_resolution,[],[f64,f1857])).

fof(f1857,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl9_136 ),
    inference(avatar_component_clause,[],[f1855])).

fof(f1855,plain,
    ( spl9_136
  <=> r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1858,plain,
    ( ~ spl9_136
    | ~ spl9_24
    | ~ spl9_116
    | spl9_122
    | ~ spl9_135 ),
    inference(avatar_split_clause,[],[f1853,f1832,f1556,f1481,f312,f1855])).

fof(f312,plain,
    ( spl9_24
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f1481,plain,
    ( spl9_116
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f1556,plain,
    ( spl9_122
  <=> r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f1832,plain,
    ( spl9_135
  <=> k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f1853,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ spl9_24
    | ~ spl9_116
    | spl9_122
    | ~ spl9_135 ),
    inference(forward_demodulation,[],[f1842,f1500])).

fof(f1500,plain,
    ( ! [X10,X9] : k1_xboole_0 = k8_relset_1(X9,X10,k1_xboole_0,X10)
    | ~ spl9_24
    | ~ spl9_116 ),
    inference(forward_demodulation,[],[f1492,f431])).

fof(f431,plain,
    ( ! [X2,X3] : k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f426,f314])).

fof(f314,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f312])).

fof(f426,plain,(
    ! [X2,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(resolution,[],[f390,f64])).

fof(f390,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | k1_relat_1(X4) = k1_relset_1(X2,X3,X4) ) ),
    inference(resolution,[],[f110,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1492,plain,
    ( ! [X10,X9] : k1_relset_1(X9,X10,k1_xboole_0) = k8_relset_1(X9,X10,k1_xboole_0,X10)
    | ~ spl9_116 ),
    inference(resolution,[],[f1482,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f1482,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl9_116 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1842,plain,
    ( ~ r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | spl9_122
    | ~ spl9_135 ),
    inference(backward_demodulation,[],[f1558,f1834])).

fof(f1834,plain,
    ( k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)
    | ~ spl9_135 ),
    inference(avatar_component_clause,[],[f1832])).

fof(f1558,plain,
    ( ~ r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | spl9_122 ),
    inference(avatar_component_clause,[],[f1556])).

fof(f1835,plain,
    ( spl9_135
    | ~ spl9_10
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f1824,f1810,f165,f1832])).

fof(f165,plain,
    ( spl9_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f1810,plain,
    ( spl9_134
  <=> v1_xboole_0(sK6(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f1824,plain,
    ( k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)
    | ~ spl9_10
    | ~ spl9_134 ),
    inference(resolution,[],[f1812,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_10 ),
    inference(resolution,[],[f104,f167])).

fof(f167,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f1812,plain,
    ( v1_xboole_0(sK6(sK0,sK1,k1_xboole_0))
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f1810])).

fof(f1813,plain,
    ( spl9_134
    | ~ spl9_133 ),
    inference(avatar_split_clause,[],[f1808,f1805,f1810])).

fof(f1805,plain,
    ( spl9_133
  <=> ! [X0] : ~ r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f1808,plain,
    ( v1_xboole_0(sK6(sK0,sK1,k1_xboole_0))
    | ~ spl9_133 ),
    inference(resolution,[],[f1806,f90])).

fof(f90,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1806,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0))
    | ~ spl9_133 ),
    inference(avatar_component_clause,[],[f1805])).

fof(f1807,plain,
    ( spl9_133
    | ~ spl9_1
    | ~ spl9_21
    | ~ spl9_3
    | ~ spl9_100
    | ~ spl9_99
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_60
    | ~ spl9_79
    | spl9_88 ),
    inference(avatar_split_clause,[],[f1803,f1082,f889,f713,f197,f165,f1202,f1206,f130,f256,f120,f1805])).

fof(f120,plain,
    ( spl9_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f256,plain,
    ( spl9_21
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f130,plain,
    ( spl9_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f1206,plain,
    ( spl9_100
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f1202,plain,
    ( spl9_99
  <=> v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f197,plain,
    ( spl9_14
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f713,plain,
    ( spl9_60
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f889,plain,
    ( spl9_79
  <=> ! [X3,X2] :
        ( m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1)))
        | v5_pre_topc(X3,X2,sK1)
        | ~ v2_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f1082,plain,
    ( spl9_88
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f1803,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0)) )
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_60
    | ~ spl9_79
    | spl9_88 ),
    inference(forward_demodulation,[],[f1802,f199])).

fof(f199,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f197])).

fof(f1802,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(sK0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0)) )
    | ~ spl9_10
    | ~ spl9_60
    | ~ spl9_79
    | spl9_88 ),
    inference(resolution,[],[f1780,f1084])).

fof(f1084,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl9_88 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1780,plain,
    ( ! [X2,X0,X1] :
        ( v5_pre_topc(X0,X1,sK1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(X1)
        | ~ r2_hidden(X2,sK6(X1,sK1,X0)) )
    | ~ spl9_10
    | ~ spl9_60
    | ~ spl9_79 ),
    inference(resolution,[],[f1006,f300])).

fof(f300,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f113,f167])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1006,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0)
        | v5_pre_topc(X3,X2,sK1)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X2) )
    | ~ spl9_60
    | ~ spl9_79 ),
    inference(forward_demodulation,[],[f1005,f117])).

fof(f117,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1005,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k1_xboole_0)))
        | m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0)
        | v5_pre_topc(X3,X2,sK1)
        | ~ v2_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X2) )
    | ~ spl9_60
    | ~ spl9_79 ),
    inference(forward_demodulation,[],[f1004,f715])).

fof(f715,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f713])).

fof(f1004,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0)
        | v5_pre_topc(X3,X2,sK1)
        | ~ v2_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
        | ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X2) )
    | ~ spl9_60
    | ~ spl9_79 ),
    inference(forward_demodulation,[],[f995,f715])).

fof(f995,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0)
        | m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1)))
        | v5_pre_topc(X3,X2,sK1)
        | ~ v2_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
        | ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X2) )
    | ~ spl9_60
    | ~ spl9_79 ),
    inference(backward_demodulation,[],[f890,f715])).

fof(f890,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1)))
        | v5_pre_topc(X3,X2,sK1)
        | ~ v2_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
        | ~ v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ l1_pre_topc(X2) )
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f889])).

fof(f1559,plain,
    ( ~ spl9_122
    | ~ spl9_30
    | spl9_114
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f1554,f1481,f1401,f478,f1556])).

fof(f478,plain,
    ( spl9_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f1401,plain,
    ( spl9_114
  <=> r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f1554,plain,
    ( ~ r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ spl9_30
    | spl9_114
    | ~ spl9_116 ),
    inference(backward_demodulation,[],[f1403,f1550])).

fof(f1550,plain,
    ( ! [X6,X5] : k8_relset_1(k2_struct_0(sK0),X5,k1_xboole_0,X6) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X5,k1_xboole_0,X6))
    | ~ spl9_30
    | ~ spl9_116 ),
    inference(resolution,[],[f483,f1482])).

fof(f483,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X1)))
        | k8_relset_1(k2_struct_0(sK0),X1,X2,X3) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X1,X2,X3)) )
    | ~ spl9_30 ),
    inference(resolution,[],[f479,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f479,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f478])).

fof(f1403,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | spl9_114 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1483,plain,
    ( spl9_116
    | ~ spl9_100
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1479,f312,f1206,f1481])).

fof(f1479,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f1478,f117])).

fof(f1478,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) )
    | ~ spl9_24 ),
    inference(superposition,[],[f114,f1476])).

fof(f1476,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f1470,f314])).

fof(f1470,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f555,f117])).

fof(f555,plain,(
    ! [X0,X1] : k1_relat_1(k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) ),
    inference(forward_demodulation,[],[f548,f389])).

fof(f389,plain,(
    ! [X0,X1] : k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f110,f169])).

fof(f169,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f66,f65])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f548,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) ),
    inference(resolution,[],[f112,f169])).

fof(f1405,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 != sK2
    | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1404,plain,
    ( ~ spl9_3
    | ~ spl9_21
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_1
    | ~ spl9_99
    | ~ spl9_100
    | ~ spl9_114
    | ~ spl9_14
    | ~ spl9_62
    | spl9_88 ),
    inference(avatar_split_clause,[],[f1399,f1082,f735,f197,f1401,f1206,f1202,f120,f140,f135,f256,f130])).

fof(f135,plain,
    ( spl9_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f140,plain,
    ( spl9_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f735,plain,
    ( spl9_62
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f1399,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_62
    | spl9_88 ),
    inference(forward_demodulation,[],[f1398,f199])).

fof(f1398,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_62
    | spl9_88 ),
    inference(forward_demodulation,[],[f1397,f737])).

fof(f737,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f735])).

fof(f1397,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_62
    | spl9_88 ),
    inference(forward_demodulation,[],[f1396,f117])).

fof(f1396,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_62
    | spl9_88 ),
    inference(forward_demodulation,[],[f1395,f737])).

fof(f1395,plain,
    ( ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_62
    | spl9_88 ),
    inference(forward_demodulation,[],[f1394,f199])).

fof(f1394,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_62
    | spl9_88 ),
    inference(forward_demodulation,[],[f1393,f737])).

fof(f1393,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))
    | ~ v2_pre_topc(sK0)
    | spl9_88 ),
    inference(resolution,[],[f89,f1084])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(f1369,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1085,plain,
    ( ~ spl9_88
    | spl9_6
    | ~ spl9_87 ),
    inference(avatar_split_clause,[],[f1064,f1049,f145,f1082])).

fof(f145,plain,
    ( spl9_6
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1049,plain,
    ( spl9_87
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f1064,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl9_6
    | ~ spl9_87 ),
    inference(backward_demodulation,[],[f147,f1051])).

fof(f1051,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f147,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1052,plain,
    ( spl9_87
    | ~ spl9_65 ),
    inference(avatar_split_clause,[],[f1045,f752,f1049])).

fof(f752,plain,
    ( spl9_65
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f1045,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_65 ),
    inference(resolution,[],[f754,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f754,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl9_65 ),
    inference(avatar_component_clause,[],[f752])).

fof(f964,plain,
    ( ~ spl9_19
    | spl9_82 ),
    inference(avatar_split_clause,[],[f961,f956,f226])).

fof(f226,plain,
    ( spl9_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f956,plain,
    ( spl9_82
  <=> m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f961,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl9_82 ),
    inference(resolution,[],[f958,f114])).

fof(f958,plain,
    ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_82 ),
    inference(avatar_component_clause,[],[f956])).

fof(f959,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_1
    | ~ spl9_82
    | ~ spl9_14
    | spl9_81 ),
    inference(avatar_split_clause,[],[f954,f949,f197,f956,f120,f130,f125])).

fof(f125,plain,
    ( spl9_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f949,plain,
    ( spl9_81
  <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f954,plain,
    ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ spl9_14
    | spl9_81 ),
    inference(forward_demodulation,[],[f953,f199])).

fof(f953,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | spl9_81 ),
    inference(resolution,[],[f951,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f951,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | spl9_81 ),
    inference(avatar_component_clause,[],[f949])).

fof(f952,plain,
    ( ~ spl9_1
    | spl9_60
    | ~ spl9_9
    | ~ spl9_4
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_81
    | spl9_6
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f947,f202,f197,f145,f949,f226,f220,f135,f160,f713,f120])).

fof(f160,plain,
    ( spl9_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f220,plain,
    ( spl9_18
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f202,plain,
    ( spl9_15
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f947,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | spl9_6
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f946,f199])).

fof(f946,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | spl9_6
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f945,f204])).

fof(f204,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f202])).

fof(f945,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl9_6
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f944,f199])).

fof(f944,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl9_6
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f943,f204])).

fof(f943,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl9_6
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f942,f199])).

fof(f942,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl9_6
    | ~ spl9_15 ),
    inference(forward_demodulation,[],[f941,f204])).

fof(f941,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | spl9_6 ),
    inference(resolution,[],[f73,f147])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f891,plain,
    ( ~ spl9_4
    | ~ spl9_5
    | spl9_79
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f883,f202,f889,f140,f135])).

fof(f883,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1))))
        | ~ v2_pre_topc(X2)
        | v5_pre_topc(X3,X2,sK1) )
    | ~ spl9_15 ),
    inference(superposition,[],[f88,f204])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f755,plain,
    ( spl9_65
    | ~ spl9_20
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f750,f713,f234,f752])).

fof(f234,plain,
    ( spl9_20
  <=> r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f750,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl9_20
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f723,f117])).

fof(f723,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))
    | ~ spl9_20
    | ~ spl9_60 ),
    inference(backward_demodulation,[],[f236,f715])).

fof(f236,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f234])).

fof(f738,plain,
    ( spl9_62
    | ~ spl9_15
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f720,f713,f202,f735])).

fof(f720,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl9_15
    | ~ spl9_60 ),
    inference(backward_demodulation,[],[f204,f715])).

fof(f655,plain,(
    spl9_48 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | spl9_48 ),
    inference(unit_resulting_resolution,[],[f115,f621,f99])).

fof(f621,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))
    | spl9_48 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl9_48
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f480,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_1
    | spl9_30
    | ~ spl9_1
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f476,f197,f120,f478,f120,f130,f125])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v1_tdlat_3(sK0) )
    | ~ spl9_1
    | ~ spl9_14 ),
    inference(duplicate_literal_removal,[],[f475])).

fof(f475,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v1_tdlat_3(sK0) )
    | ~ spl9_1
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f474,f199])).

fof(f474,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ v1_tdlat_3(sK0) )
    | ~ spl9_1
    | ~ spl9_14 ),
    inference(resolution,[],[f472,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f472,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl9_1
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f470,f199])).

fof(f470,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl9_1 ),
    inference(resolution,[],[f79,f122])).

fof(f122,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f324,plain,(
    spl9_25 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl9_25 ),
    inference(unit_resulting_resolution,[],[f251,f318])).

fof(f318,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | spl9_25 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl9_25
  <=> v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f251,plain,(
    ! [X2] : v4_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[],[f107,f246])).

fof(f246,plain,(
    ! [X0] : k1_xboole_0 = sK8(X0,k1_xboole_0) ),
    inference(resolution,[],[f245,f80])).

fof(f245,plain,(
    ! [X0] : r1_tarski(sK8(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f243,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f243,plain,(
    ! [X0] : m1_subset_1(sK8(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f105,f117])).

fof(f105,plain,(
    ! [X0,X1] : m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f107,plain,(
    ! [X0,X1] : v4_relat_1(sK8(X0,X1),X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f319,plain,
    ( spl9_24
    | ~ spl9_25
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f310,f185,f316,f312])).

fof(f185,plain,
    ( spl9_13
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f310,plain,
    ( ~ v4_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl9_13 ),
    inference(resolution,[],[f266,f187])).

fof(f187,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f266,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f94,f80])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f259,plain,(
    spl9_21 ),
    inference(avatar_split_clause,[],[f252,f256])).

fof(f252,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f108,f246])).

fof(f108,plain,(
    ! [X0,X1] : v1_funct_1(sK8(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f237,plain,
    ( spl9_20
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f232,f226,f234])).

fof(f232,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl9_19 ),
    inference(resolution,[],[f100,f228])).

fof(f228,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f226])).

fof(f229,plain,
    ( spl9_19
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f224,f209,f197,f226])).

fof(f209,plain,
    ( spl9_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f224,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f211,f199])).

fof(f211,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f209])).

fof(f223,plain,
    ( spl9_18
    | ~ spl9_14
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f218,f214,f197,f220])).

fof(f214,plain,
    ( spl9_17
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f218,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl9_14
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f216,f199])).

fof(f216,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f214])).

fof(f217,plain,
    ( spl9_17
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f207,f202,f155,f214])).

fof(f155,plain,
    ( spl9_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f207,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f157,f204])).

fof(f157,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f212,plain,
    ( spl9_16
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f206,f202,f150,f209])).

fof(f150,plain,
    ( spl9_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f206,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f152,f204])).

fof(f152,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f150])).

fof(f205,plain,
    ( spl9_15
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f195,f178,f202])).

fof(f178,plain,
    ( spl9_12
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f195,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl9_12 ),
    inference(resolution,[],[f67,f180])).

fof(f180,plain,
    ( l1_struct_0(sK1)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f200,plain,
    ( spl9_14
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f194,f173,f197])).

fof(f173,plain,
    ( spl9_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f194,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_11 ),
    inference(resolution,[],[f67,f175])).

fof(f175,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f188,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f183,f185])).

fof(f183,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f92,f117])).

fof(f92,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f181,plain,
    ( spl9_12
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f171,f135,f178])).

fof(f171,plain,
    ( l1_struct_0(sK1)
    | ~ spl9_4 ),
    inference(resolution,[],[f68,f137])).

fof(f137,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f135])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f176,plain,
    ( spl9_11
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f170,f120,f173])).

fof(f170,plain,
    ( l1_struct_0(sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f68,f122])).

fof(f168,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f63,f165])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f163,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f54,f160])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(f158,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f55,f155])).

fof(f55,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f153,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f56,f150])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f148,plain,(
    ~ spl9_6 ),
    inference(avatar_split_clause,[],[f57,f145])).

fof(f57,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f143,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f58,f140])).

fof(f58,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f138,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f59,f135])).

fof(f59,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f133,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f60,f130])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f128,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f61,f125])).

fof(f61,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f123,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f62,f120])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (19316)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (19308)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (19308)Refutation not found, incomplete strategy% (19308)------------------------------
% 0.22/0.50  % (19308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19308)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19308)Memory used [KB]: 6140
% 0.22/0.50  % (19308)Time elapsed: 0.086 s
% 0.22/0.50  % (19308)------------------------------
% 0.22/0.50  % (19308)------------------------------
% 0.22/0.50  % (19297)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (19295)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (19295)Refutation not found, incomplete strategy% (19295)------------------------------
% 0.22/0.50  % (19295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19295)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (19295)Memory used [KB]: 10490
% 0.22/0.50  % (19295)Time elapsed: 0.002 s
% 0.22/0.50  % (19295)------------------------------
% 0.22/0.50  % (19295)------------------------------
% 0.22/0.50  % (19300)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (19302)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (19299)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (19319)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (19314)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (19318)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (19311)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (19305)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (19306)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (19306)Refutation not found, incomplete strategy% (19306)------------------------------
% 0.22/0.52  % (19306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19306)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19306)Memory used [KB]: 10490
% 0.22/0.52  % (19306)Time elapsed: 0.002 s
% 0.22/0.52  % (19306)------------------------------
% 0.22/0.52  % (19306)------------------------------
% 0.22/0.52  % (19312)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (19307)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (19296)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (19303)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (19310)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (19300)Refutation not found, incomplete strategy% (19300)------------------------------
% 0.22/0.53  % (19300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19300)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19300)Memory used [KB]: 6524
% 0.22/0.53  % (19300)Time elapsed: 0.109 s
% 0.22/0.53  % (19300)------------------------------
% 0.22/0.53  % (19300)------------------------------
% 0.22/0.53  % (19298)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (19317)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (19301)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.34/0.54  % (19320)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.34/0.54  % (19301)Refutation not found, incomplete strategy% (19301)------------------------------
% 1.34/0.54  % (19301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (19301)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (19301)Memory used [KB]: 10746
% 1.34/0.54  % (19301)Time elapsed: 0.127 s
% 1.34/0.54  % (19301)------------------------------
% 1.34/0.54  % (19301)------------------------------
% 1.34/0.54  % (19309)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.34/0.55  % (19313)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.34/0.55  % (19304)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.34/0.55  % (19315)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.57/0.64  % (19310)Refutation found. Thanks to Tanya!
% 1.57/0.64  % SZS status Theorem for theBenchmark
% 1.57/0.64  % SZS output start Proof for theBenchmark
% 1.57/0.64  fof(f1901,plain,(
% 1.57/0.64    $false),
% 1.57/0.64    inference(avatar_sat_refutation,[],[f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f176,f181,f188,f200,f205,f212,f217,f223,f229,f237,f259,f319,f324,f480,f655,f738,f755,f891,f952,f959,f964,f1052,f1085,f1369,f1404,f1405,f1483,f1559,f1807,f1813,f1835,f1858,f1899])).
% 1.57/0.64  fof(f1899,plain,(
% 1.57/0.64    spl9_136),
% 1.57/0.64    inference(avatar_contradiction_clause,[],[f1895])).
% 1.57/0.64  fof(f1895,plain,(
% 1.57/0.64    $false | spl9_136),
% 1.57/0.64    inference(unit_resulting_resolution,[],[f64,f1857])).
% 1.57/0.64  fof(f1857,plain,(
% 1.57/0.64    ~r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | spl9_136),
% 1.57/0.64    inference(avatar_component_clause,[],[f1855])).
% 1.57/0.64  fof(f1855,plain,(
% 1.57/0.64    spl9_136 <=> r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))),
% 1.57/0.64    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).
% 2.17/0.65  fof(f64,plain,(
% 2.17/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.17/0.65    inference(cnf_transformation,[],[f4])).
% 2.17/0.65  fof(f4,axiom,(
% 2.17/0.65    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.17/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.17/0.65  fof(f1858,plain,(
% 2.17/0.65    ~spl9_136 | ~spl9_24 | ~spl9_116 | spl9_122 | ~spl9_135),
% 2.17/0.65    inference(avatar_split_clause,[],[f1853,f1832,f1556,f1481,f312,f1855])).
% 2.17/0.65  fof(f312,plain,(
% 2.17/0.65    spl9_24 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 2.17/0.65  fof(f1481,plain,(
% 2.17/0.65    spl9_116 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).
% 2.17/0.65  fof(f1556,plain,(
% 2.17/0.65    spl9_122 <=> r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).
% 2.17/0.65  fof(f1832,plain,(
% 2.17/0.65    spl9_135 <=> k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)),
% 2.17/0.65    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).
% 2.17/0.65  fof(f1853,plain,(
% 2.17/0.65    ~r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (~spl9_24 | ~spl9_116 | spl9_122 | ~spl9_135)),
% 2.17/0.65    inference(forward_demodulation,[],[f1842,f1500])).
% 2.17/0.65  fof(f1500,plain,(
% 2.17/0.65    ( ! [X10,X9] : (k1_xboole_0 = k8_relset_1(X9,X10,k1_xboole_0,X10)) ) | (~spl9_24 | ~spl9_116)),
% 2.17/0.65    inference(forward_demodulation,[],[f1492,f431])).
% 2.17/0.66  fof(f431,plain,(
% 2.17/0.66    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)) ) | ~spl9_24),
% 2.17/0.66    inference(forward_demodulation,[],[f426,f314])).
% 2.17/0.66  fof(f314,plain,(
% 2.17/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_24),
% 2.17/0.66    inference(avatar_component_clause,[],[f312])).
% 2.17/0.66  fof(f426,plain,(
% 2.17/0.66    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 2.17/0.66    inference(resolution,[],[f390,f64])).
% 2.17/0.66  fof(f390,plain,(
% 2.17/0.66    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | k1_relat_1(X4) = k1_relset_1(X2,X3,X4)) )),
% 2.17/0.66    inference(resolution,[],[f110,f99])).
% 2.17/0.66  fof(f99,plain,(
% 2.17/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f10])).
% 2.17/0.66  fof(f10,axiom,(
% 2.17/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.17/0.66  fof(f110,plain,(
% 2.17/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f50])).
% 2.17/0.66  fof(f50,plain,(
% 2.17/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.66    inference(ennf_transformation,[],[f16])).
% 2.17/0.66  fof(f16,axiom,(
% 2.17/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.17/0.66  fof(f1492,plain,(
% 2.17/0.66    ( ! [X10,X9] : (k1_relset_1(X9,X10,k1_xboole_0) = k8_relset_1(X9,X10,k1_xboole_0,X10)) ) | ~spl9_116),
% 2.17/0.66    inference(resolution,[],[f1482,f112])).
% 2.17/0.66  fof(f112,plain,(
% 2.17/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f51])).
% 2.17/0.66  fof(f51,plain,(
% 2.17/0.66    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.66    inference(ennf_transformation,[],[f17])).
% 2.17/0.66  fof(f17,axiom,(
% 2.17/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 2.17/0.66  fof(f1482,plain,(
% 2.17/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl9_116),
% 2.17/0.66    inference(avatar_component_clause,[],[f1481])).
% 2.17/0.66  fof(f1842,plain,(
% 2.17/0.66    ~r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | (spl9_122 | ~spl9_135)),
% 2.17/0.66    inference(backward_demodulation,[],[f1558,f1834])).
% 2.17/0.66  fof(f1834,plain,(
% 2.17/0.66    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) | ~spl9_135),
% 2.17/0.66    inference(avatar_component_clause,[],[f1832])).
% 2.17/0.66  fof(f1558,plain,(
% 2.17/0.66    ~r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | spl9_122),
% 2.17/0.66    inference(avatar_component_clause,[],[f1556])).
% 2.17/0.66  fof(f1835,plain,(
% 2.17/0.66    spl9_135 | ~spl9_10 | ~spl9_134),
% 2.17/0.66    inference(avatar_split_clause,[],[f1824,f1810,f165,f1832])).
% 2.17/0.66  fof(f165,plain,(
% 2.17/0.66    spl9_10 <=> v1_xboole_0(k1_xboole_0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 2.17/0.66  fof(f1810,plain,(
% 2.17/0.66    spl9_134 <=> v1_xboole_0(sK6(sK0,sK1,k1_xboole_0))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).
% 2.17/0.66  fof(f1824,plain,(
% 2.17/0.66    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) | (~spl9_10 | ~spl9_134)),
% 2.17/0.66    inference(resolution,[],[f1812,f238])).
% 2.17/0.66  fof(f238,plain,(
% 2.17/0.66    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl9_10),
% 2.17/0.66    inference(resolution,[],[f104,f167])).
% 2.17/0.66  fof(f167,plain,(
% 2.17/0.66    v1_xboole_0(k1_xboole_0) | ~spl9_10),
% 2.17/0.66    inference(avatar_component_clause,[],[f165])).
% 2.17/0.66  fof(f104,plain,(
% 2.17/0.66    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_xboole_0(X0) | X0 = X1) )),
% 2.17/0.66    inference(cnf_transformation,[],[f49])).
% 2.17/0.66  fof(f49,plain,(
% 2.17/0.66    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f6])).
% 2.17/0.66  fof(f6,axiom,(
% 2.17/0.66    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 2.17/0.66  fof(f1812,plain,(
% 2.17/0.66    v1_xboole_0(sK6(sK0,sK1,k1_xboole_0)) | ~spl9_134),
% 2.17/0.66    inference(avatar_component_clause,[],[f1810])).
% 2.17/0.66  fof(f1813,plain,(
% 2.17/0.66    spl9_134 | ~spl9_133),
% 2.17/0.66    inference(avatar_split_clause,[],[f1808,f1805,f1810])).
% 2.17/0.66  fof(f1805,plain,(
% 2.17/0.66    spl9_133 <=> ! [X0] : ~r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).
% 2.17/0.66  fof(f1808,plain,(
% 2.17/0.66    v1_xboole_0(sK6(sK0,sK1,k1_xboole_0)) | ~spl9_133),
% 2.17/0.66    inference(resolution,[],[f1806,f90])).
% 2.17/0.66  fof(f90,plain,(
% 2.17/0.66    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f1])).
% 2.17/0.66  fof(f1,axiom,(
% 2.17/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.17/0.66  fof(f1806,plain,(
% 2.17/0.66    ( ! [X0] : (~r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0))) ) | ~spl9_133),
% 2.17/0.66    inference(avatar_component_clause,[],[f1805])).
% 2.17/0.66  fof(f1807,plain,(
% 2.17/0.66    spl9_133 | ~spl9_1 | ~spl9_21 | ~spl9_3 | ~spl9_100 | ~spl9_99 | ~spl9_10 | ~spl9_14 | ~spl9_60 | ~spl9_79 | spl9_88),
% 2.17/0.66    inference(avatar_split_clause,[],[f1803,f1082,f889,f713,f197,f165,f1202,f1206,f130,f256,f120,f1805])).
% 2.17/0.66  fof(f120,plain,(
% 2.17/0.66    spl9_1 <=> l1_pre_topc(sK0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.17/0.66  fof(f256,plain,(
% 2.17/0.66    spl9_21 <=> v1_funct_1(k1_xboole_0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 2.17/0.66  fof(f130,plain,(
% 2.17/0.66    spl9_3 <=> v2_pre_topc(sK0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 2.17/0.66  fof(f1206,plain,(
% 2.17/0.66    spl9_100 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).
% 2.17/0.66  fof(f1202,plain,(
% 2.17/0.66    spl9_99 <=> v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).
% 2.17/0.66  fof(f197,plain,(
% 2.17/0.66    spl9_14 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 2.17/0.66  fof(f713,plain,(
% 2.17/0.66    spl9_60 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).
% 2.17/0.66  fof(f889,plain,(
% 2.17/0.66    spl9_79 <=> ! [X3,X2] : (m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1))) | v5_pre_topc(X3,X2,sK1) | ~v2_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).
% 2.17/0.66  fof(f1082,plain,(
% 2.17/0.66    spl9_88 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 2.17/0.66  fof(f1803,plain,(
% 2.17/0.66    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(sK0) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0))) ) | (~spl9_10 | ~spl9_14 | ~spl9_60 | ~spl9_79 | spl9_88)),
% 2.17/0.66    inference(forward_demodulation,[],[f1802,f199])).
% 2.17/0.66  fof(f199,plain,(
% 2.17/0.66    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl9_14),
% 2.17/0.66    inference(avatar_component_clause,[],[f197])).
% 2.17/0.66  fof(f1802,plain,(
% 2.17/0.66    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(sK0) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK0) | ~r2_hidden(X0,sK6(sK0,sK1,k1_xboole_0))) ) | (~spl9_10 | ~spl9_60 | ~spl9_79 | spl9_88)),
% 2.17/0.66    inference(resolution,[],[f1780,f1084])).
% 2.17/0.66  fof(f1084,plain,(
% 2.17/0.66    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl9_88),
% 2.17/0.66    inference(avatar_component_clause,[],[f1082])).
% 2.17/0.66  fof(f1780,plain,(
% 2.17/0.66    ( ! [X2,X0,X1] : (v5_pre_topc(X0,X1,sK1) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(X1) | ~v1_funct_1(X0) | ~l1_pre_topc(X1) | ~r2_hidden(X2,sK6(X1,sK1,X0))) ) | (~spl9_10 | ~spl9_60 | ~spl9_79)),
% 2.17/0.66    inference(resolution,[],[f1006,f300])).
% 2.17/0.66  fof(f300,plain,(
% 2.17/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl9_10),
% 2.17/0.66    inference(resolution,[],[f113,f167])).
% 2.17/0.66  fof(f113,plain,(
% 2.17/0.66    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f52])).
% 2.17/0.66  fof(f52,plain,(
% 2.17/0.66    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.17/0.66    inference(ennf_transformation,[],[f11])).
% 2.17/0.66  fof(f11,axiom,(
% 2.17/0.66    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 2.17/0.66  fof(f1006,plain,(
% 2.17/0.66    ( ! [X2,X3] : (m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0) | v5_pre_topc(X3,X2,sK1) | ~v2_pre_topc(X2) | ~v1_funct_1(X3) | ~l1_pre_topc(X2)) ) | (~spl9_60 | ~spl9_79)),
% 2.17/0.66    inference(forward_demodulation,[],[f1005,f117])).
% 2.17/0.66  fof(f117,plain,(
% 2.17/0.66    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.17/0.66    inference(equality_resolution,[],[f103])).
% 2.17/0.66  fof(f103,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f7])).
% 2.17/0.66  fof(f7,axiom,(
% 2.17/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.17/0.66  fof(f1005,plain,(
% 2.17/0.66    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k1_xboole_0))) | m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0) | v5_pre_topc(X3,X2,sK1) | ~v2_pre_topc(X2) | ~v1_funct_1(X3) | ~l1_pre_topc(X2)) ) | (~spl9_60 | ~spl9_79)),
% 2.17/0.66    inference(forward_demodulation,[],[f1004,f715])).
% 2.17/0.66  fof(f715,plain,(
% 2.17/0.66    k1_xboole_0 = k2_struct_0(sK1) | ~spl9_60),
% 2.17/0.66    inference(avatar_component_clause,[],[f713])).
% 2.17/0.66  fof(f1004,plain,(
% 2.17/0.66    ( ! [X2,X3] : (m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0) | v5_pre_topc(X3,X2,sK1) | ~v2_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~v1_funct_1(X3) | ~l1_pre_topc(X2)) ) | (~spl9_60 | ~spl9_79)),
% 2.17/0.66    inference(forward_demodulation,[],[f995,f715])).
% 2.17/0.66  fof(f995,plain,(
% 2.17/0.66    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(X2),k1_xboole_0) | m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1))) | v5_pre_topc(X3,X2,sK1) | ~v2_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~v1_funct_1(X3) | ~l1_pre_topc(X2)) ) | (~spl9_60 | ~spl9_79)),
% 2.17/0.66    inference(backward_demodulation,[],[f890,f715])).
% 2.17/0.66  fof(f890,plain,(
% 2.17/0.66    ( ! [X2,X3] : (m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1))) | v5_pre_topc(X3,X2,sK1) | ~v2_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2)) ) | ~spl9_79),
% 2.17/0.66    inference(avatar_component_clause,[],[f889])).
% 2.17/0.66  fof(f1559,plain,(
% 2.17/0.66    ~spl9_122 | ~spl9_30 | spl9_114 | ~spl9_116),
% 2.17/0.66    inference(avatar_split_clause,[],[f1554,f1481,f1401,f478,f1556])).
% 2.17/0.66  fof(f478,plain,(
% 2.17/0.66    spl9_30 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 2.17/0.66  fof(f1401,plain,(
% 2.17/0.66    spl9_114 <=> r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0))))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).
% 2.17/0.66  fof(f1554,plain,(
% 2.17/0.66    ~r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | (~spl9_30 | spl9_114 | ~spl9_116)),
% 2.17/0.66    inference(backward_demodulation,[],[f1403,f1550])).
% 2.17/0.66  fof(f1550,plain,(
% 2.17/0.66    ( ! [X6,X5] : (k8_relset_1(k2_struct_0(sK0),X5,k1_xboole_0,X6) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X5,k1_xboole_0,X6))) ) | (~spl9_30 | ~spl9_116)),
% 2.17/0.66    inference(resolution,[],[f483,f1482])).
% 2.17/0.66  fof(f483,plain,(
% 2.17/0.66    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X1))) | k8_relset_1(k2_struct_0(sK0),X1,X2,X3) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X1,X2,X3))) ) | ~spl9_30),
% 2.17/0.66    inference(resolution,[],[f479,f114])).
% 2.17/0.66  fof(f114,plain,(
% 2.17/0.66    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f53])).
% 2.17/0.66  fof(f53,plain,(
% 2.17/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.66    inference(ennf_transformation,[],[f15])).
% 2.17/0.66  fof(f15,axiom,(
% 2.17/0.66    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 2.17/0.66  fof(f479,plain,(
% 2.17/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl9_30),
% 2.17/0.66    inference(avatar_component_clause,[],[f478])).
% 2.17/0.66  fof(f1403,plain,(
% 2.17/0.66    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | spl9_114),
% 2.17/0.66    inference(avatar_component_clause,[],[f1401])).
% 2.17/0.66  fof(f1483,plain,(
% 2.17/0.66    spl9_116 | ~spl9_100 | ~spl9_24),
% 2.17/0.66    inference(avatar_split_clause,[],[f1479,f312,f1206,f1481])).
% 2.17/0.66  fof(f1479,plain,(
% 2.17/0.66    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl9_24),
% 2.17/0.66    inference(forward_demodulation,[],[f1478,f117])).
% 2.17/0.66  fof(f1478,plain,(
% 2.17/0.66    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | ~spl9_24),
% 2.17/0.66    inference(superposition,[],[f114,f1476])).
% 2.17/0.66  fof(f1476,plain,(
% 2.17/0.66    ( ! [X0] : (k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ) | ~spl9_24),
% 2.17/0.66    inference(forward_demodulation,[],[f1470,f314])).
% 2.17/0.66  fof(f1470,plain,(
% 2.17/0.66    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 2.17/0.66    inference(superposition,[],[f555,f117])).
% 2.17/0.66  fof(f555,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1)) )),
% 2.17/0.66    inference(forward_demodulation,[],[f548,f389])).
% 2.17/0.66  fof(f389,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 2.17/0.66    inference(resolution,[],[f110,f169])).
% 2.17/0.66  fof(f169,plain,(
% 2.17/0.66    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.17/0.66    inference(forward_demodulation,[],[f66,f65])).
% 2.17/0.66  fof(f65,plain,(
% 2.17/0.66    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.17/0.66    inference(cnf_transformation,[],[f8])).
% 2.17/0.66  fof(f8,axiom,(
% 2.17/0.66    ! [X0] : k2_subset_1(X0) = X0),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.17/0.66  fof(f66,plain,(
% 2.17/0.66    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f9])).
% 2.17/0.66  fof(f9,axiom,(
% 2.17/0.66    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.17/0.66  fof(f548,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1)) )),
% 2.17/0.66    inference(resolution,[],[f112,f169])).
% 2.17/0.66  fof(f1405,plain,(
% 2.17/0.66    u1_struct_0(sK1) != k2_struct_0(sK1) | u1_struct_0(sK0) != k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 != sK2 | v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.17/0.66    introduced(theory_tautology_sat_conflict,[])).
% 2.17/0.66  fof(f1404,plain,(
% 2.17/0.66    ~spl9_3 | ~spl9_21 | ~spl9_4 | ~spl9_5 | ~spl9_1 | ~spl9_99 | ~spl9_100 | ~spl9_114 | ~spl9_14 | ~spl9_62 | spl9_88),
% 2.17/0.66    inference(avatar_split_clause,[],[f1399,f1082,f735,f197,f1401,f1206,f1202,f120,f140,f135,f256,f130])).
% 2.17/0.66  fof(f135,plain,(
% 2.17/0.66    spl9_4 <=> l1_pre_topc(sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 2.17/0.66  fof(f140,plain,(
% 2.17/0.66    spl9_5 <=> v2_pre_topc(sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.17/0.66  fof(f735,plain,(
% 2.17/0.66    spl9_62 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 2.17/0.66  fof(f1399,plain,(
% 2.17/0.66    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl9_14 | ~spl9_62 | spl9_88)),
% 2.17/0.66    inference(forward_demodulation,[],[f1398,f199])).
% 2.17/0.66  fof(f1398,plain,(
% 2.17/0.66    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl9_14 | ~spl9_62 | spl9_88)),
% 2.17/0.66    inference(forward_demodulation,[],[f1397,f737])).
% 2.17/0.66  fof(f737,plain,(
% 2.17/0.66    k1_xboole_0 = u1_struct_0(sK1) | ~spl9_62),
% 2.17/0.66    inference(avatar_component_clause,[],[f735])).
% 2.17/0.66  fof(f1397,plain,(
% 2.17/0.66    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~v2_pre_topc(sK0) | (~spl9_14 | ~spl9_62 | spl9_88)),
% 2.17/0.66    inference(forward_demodulation,[],[f1396,f117])).
% 2.17/0.66  fof(f1396,plain,(
% 2.17/0.66    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~v2_pre_topc(sK0) | (~spl9_14 | ~spl9_62 | spl9_88)),
% 2.17/0.66    inference(forward_demodulation,[],[f1395,f737])).
% 2.17/0.66  fof(f1395,plain,(
% 2.17/0.66    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~v2_pre_topc(sK0) | (~spl9_14 | ~spl9_62 | spl9_88)),
% 2.17/0.66    inference(forward_demodulation,[],[f1394,f199])).
% 2.17/0.66  fof(f1394,plain,(
% 2.17/0.66    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~v2_pre_topc(sK0) | (~spl9_62 | spl9_88)),
% 2.17/0.66    inference(forward_demodulation,[],[f1393,f737])).
% 2.17/0.66  fof(f1393,plain,(
% 2.17/0.66    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,sK6(sK0,sK1,k1_xboole_0))),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,sK6(sK0,sK1,k1_xboole_0)))) | ~v2_pre_topc(sK0) | spl9_88),
% 2.17/0.66    inference(resolution,[],[f89,f1084])).
% 2.17/0.66  fof(f89,plain,(
% 2.17/0.66    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) | ~v2_pre_topc(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f46])).
% 2.17/0.66  fof(f46,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.17/0.66    inference(flattening,[],[f45])).
% 2.17/0.66  fof(f45,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.17/0.66    inference(ennf_transformation,[],[f23])).
% 2.17/0.66  fof(f23,axiom,(
% 2.17/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).
% 2.17/0.66  fof(f1369,plain,(
% 2.17/0.66    k1_xboole_0 != k2_struct_0(sK1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))),
% 2.17/0.66    introduced(theory_tautology_sat_conflict,[])).
% 2.17/0.66  fof(f1085,plain,(
% 2.17/0.66    ~spl9_88 | spl9_6 | ~spl9_87),
% 2.17/0.66    inference(avatar_split_clause,[],[f1064,f1049,f145,f1082])).
% 2.17/0.66  fof(f145,plain,(
% 2.17/0.66    spl9_6 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 2.17/0.66  fof(f1049,plain,(
% 2.17/0.66    spl9_87 <=> k1_xboole_0 = sK2),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).
% 2.17/0.66  fof(f1064,plain,(
% 2.17/0.66    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl9_6 | ~spl9_87)),
% 2.17/0.66    inference(backward_demodulation,[],[f147,f1051])).
% 2.17/0.66  fof(f1051,plain,(
% 2.17/0.66    k1_xboole_0 = sK2 | ~spl9_87),
% 2.17/0.66    inference(avatar_component_clause,[],[f1049])).
% 2.17/0.66  fof(f147,plain,(
% 2.17/0.66    ~v5_pre_topc(sK2,sK0,sK1) | spl9_6),
% 2.17/0.66    inference(avatar_component_clause,[],[f145])).
% 2.17/0.66  fof(f1052,plain,(
% 2.17/0.66    spl9_87 | ~spl9_65),
% 2.17/0.66    inference(avatar_split_clause,[],[f1045,f752,f1049])).
% 2.17/0.66  fof(f752,plain,(
% 2.17/0.66    spl9_65 <=> r1_tarski(sK2,k1_xboole_0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).
% 2.17/0.66  fof(f1045,plain,(
% 2.17/0.66    k1_xboole_0 = sK2 | ~spl9_65),
% 2.17/0.66    inference(resolution,[],[f754,f80])).
% 2.17/0.66  fof(f80,plain,(
% 2.17/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.17/0.66    inference(cnf_transformation,[],[f40])).
% 2.17/0.66  fof(f40,plain,(
% 2.17/0.66    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.17/0.66    inference(ennf_transformation,[],[f5])).
% 2.17/0.66  fof(f5,axiom,(
% 2.17/0.66    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.17/0.66  fof(f754,plain,(
% 2.17/0.66    r1_tarski(sK2,k1_xboole_0) | ~spl9_65),
% 2.17/0.66    inference(avatar_component_clause,[],[f752])).
% 2.17/0.66  fof(f964,plain,(
% 2.17/0.66    ~spl9_19 | spl9_82),
% 2.17/0.66    inference(avatar_split_clause,[],[f961,f956,f226])).
% 2.17/0.66  fof(f226,plain,(
% 2.17/0.66    spl9_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 2.17/0.66  fof(f956,plain,(
% 2.17/0.66    spl9_82 <=> m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).
% 2.17/0.66  fof(f961,plain,(
% 2.17/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl9_82),
% 2.17/0.66    inference(resolution,[],[f958,f114])).
% 2.17/0.66  fof(f958,plain,(
% 2.17/0.66    ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl9_82),
% 2.17/0.66    inference(avatar_component_clause,[],[f956])).
% 2.17/0.66  fof(f959,plain,(
% 2.17/0.66    ~spl9_2 | ~spl9_3 | ~spl9_1 | ~spl9_82 | ~spl9_14 | spl9_81),
% 2.17/0.66    inference(avatar_split_clause,[],[f954,f949,f197,f956,f120,f130,f125])).
% 2.17/0.66  fof(f125,plain,(
% 2.17/0.66    spl9_2 <=> v1_tdlat_3(sK0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 2.17/0.66  fof(f949,plain,(
% 2.17/0.66    spl9_81 <=> v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).
% 2.17/0.66  fof(f954,plain,(
% 2.17/0.66    ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | (~spl9_14 | spl9_81)),
% 2.17/0.66    inference(forward_demodulation,[],[f953,f199])).
% 2.17/0.66  fof(f953,plain,(
% 2.17/0.66    ~l1_pre_topc(sK0) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | spl9_81),
% 2.17/0.66    inference(resolution,[],[f951,f81])).
% 2.17/0.66  fof(f81,plain,(
% 2.17/0.66    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f42])).
% 2.17/0.66  fof(f42,plain,(
% 2.17/0.66    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.17/0.66    inference(flattening,[],[f41])).
% 2.17/0.66  fof(f41,plain,(
% 2.17/0.66    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.17/0.66    inference(ennf_transformation,[],[f25])).
% 2.17/0.66  fof(f25,axiom,(
% 2.17/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 2.17/0.66  fof(f951,plain,(
% 2.17/0.66    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | spl9_81),
% 2.17/0.66    inference(avatar_component_clause,[],[f949])).
% 2.17/0.66  fof(f952,plain,(
% 2.17/0.66    ~spl9_1 | spl9_60 | ~spl9_9 | ~spl9_4 | ~spl9_18 | ~spl9_19 | ~spl9_81 | spl9_6 | ~spl9_14 | ~spl9_15),
% 2.17/0.66    inference(avatar_split_clause,[],[f947,f202,f197,f145,f949,f226,f220,f135,f160,f713,f120])).
% 2.17/0.66  fof(f160,plain,(
% 2.17/0.66    spl9_9 <=> v1_funct_1(sK2)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 2.17/0.66  fof(f220,plain,(
% 2.17/0.66    spl9_18 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 2.17/0.66  fof(f202,plain,(
% 2.17/0.66    spl9_15 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 2.17/0.66  fof(f947,plain,(
% 2.17/0.66    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~l1_pre_topc(sK0) | (spl9_6 | ~spl9_14 | ~spl9_15)),
% 2.17/0.66    inference(forward_demodulation,[],[f946,f199])).
% 2.17/0.66  fof(f946,plain,(
% 2.17/0.66    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~l1_pre_topc(sK0) | (spl9_6 | ~spl9_14 | ~spl9_15)),
% 2.17/0.66    inference(forward_demodulation,[],[f945,f204])).
% 2.17/0.66  fof(f204,plain,(
% 2.17/0.66    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl9_15),
% 2.17/0.66    inference(avatar_component_clause,[],[f202])).
% 2.17/0.66  fof(f945,plain,(
% 2.17/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | (spl9_6 | ~spl9_14 | ~spl9_15)),
% 2.17/0.66    inference(forward_demodulation,[],[f944,f199])).
% 2.17/0.66  fof(f944,plain,(
% 2.17/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | (spl9_6 | ~spl9_14 | ~spl9_15)),
% 2.17/0.66    inference(forward_demodulation,[],[f943,f204])).
% 2.17/0.66  fof(f943,plain,(
% 2.17/0.66    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | (spl9_6 | ~spl9_14 | ~spl9_15)),
% 2.17/0.66    inference(forward_demodulation,[],[f942,f199])).
% 2.17/0.66  fof(f942,plain,(
% 2.17/0.66    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | (spl9_6 | ~spl9_15)),
% 2.17/0.66    inference(forward_demodulation,[],[f941,f204])).
% 2.17/0.66  fof(f941,plain,(
% 2.17/0.66    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK0) | spl9_6),
% 2.17/0.66    inference(resolution,[],[f73,f147])).
% 2.17/0.66  fof(f73,plain,(
% 2.17/0.66    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_xboole_0 = k2_struct_0(X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) | ~l1_pre_topc(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f37])).
% 2.17/0.66  fof(f37,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.17/0.66    inference(flattening,[],[f36])).
% 2.17/0.66  fof(f36,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f22])).
% 2.17/0.66  fof(f22,axiom,(
% 2.17/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 2.17/0.66  fof(f891,plain,(
% 2.17/0.66    ~spl9_4 | ~spl9_5 | spl9_79 | ~spl9_15),
% 2.17/0.66    inference(avatar_split_clause,[],[f883,f202,f889,f140,f135])).
% 2.17/0.66  fof(f883,plain,(
% 2.17/0.66    ( ! [X2,X3] : (m1_subset_1(sK6(X2,sK1,X3),k1_zfmisc_1(k2_struct_0(sK1))) | ~l1_pre_topc(X2) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X2),k2_struct_0(sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),k2_struct_0(sK1)))) | ~v2_pre_topc(X2) | v5_pre_topc(X3,X2,sK1)) ) | ~spl9_15),
% 2.17/0.66    inference(superposition,[],[f88,f204])).
% 2.17/0.66  fof(f88,plain,(
% 2.17/0.66    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f46])).
% 2.17/0.66  fof(f755,plain,(
% 2.17/0.66    spl9_65 | ~spl9_20 | ~spl9_60),
% 2.17/0.66    inference(avatar_split_clause,[],[f750,f713,f234,f752])).
% 2.17/0.66  fof(f234,plain,(
% 2.17/0.66    spl9_20 <=> r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 2.17/0.66  fof(f750,plain,(
% 2.17/0.66    r1_tarski(sK2,k1_xboole_0) | (~spl9_20 | ~spl9_60)),
% 2.17/0.66    inference(forward_demodulation,[],[f723,f117])).
% 2.17/0.66  fof(f723,plain,(
% 2.17/0.66    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)) | (~spl9_20 | ~spl9_60)),
% 2.17/0.66    inference(backward_demodulation,[],[f236,f715])).
% 2.17/0.66  fof(f236,plain,(
% 2.17/0.66    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | ~spl9_20),
% 2.17/0.66    inference(avatar_component_clause,[],[f234])).
% 2.17/0.66  fof(f738,plain,(
% 2.17/0.66    spl9_62 | ~spl9_15 | ~spl9_60),
% 2.17/0.66    inference(avatar_split_clause,[],[f720,f713,f202,f735])).
% 2.17/0.66  fof(f720,plain,(
% 2.17/0.66    k1_xboole_0 = u1_struct_0(sK1) | (~spl9_15 | ~spl9_60)),
% 2.17/0.66    inference(backward_demodulation,[],[f204,f715])).
% 2.17/0.66  fof(f655,plain,(
% 2.17/0.66    spl9_48),
% 2.17/0.66    inference(avatar_contradiction_clause,[],[f650])).
% 2.17/0.66  fof(f650,plain,(
% 2.17/0.66    $false | spl9_48),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f115,f621,f99])).
% 2.17/0.66  fof(f621,plain,(
% 2.17/0.66    ~m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) | spl9_48),
% 2.17/0.66    inference(avatar_component_clause,[],[f619])).
% 2.17/0.66  fof(f619,plain,(
% 2.17/0.66    spl9_48 <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1)))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 2.17/0.66  fof(f115,plain,(
% 2.17/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.17/0.66    inference(equality_resolution,[],[f97])).
% 2.17/0.66  fof(f97,plain,(
% 2.17/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.17/0.66    inference(cnf_transformation,[],[f3])).
% 2.17/0.66  fof(f3,axiom,(
% 2.17/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.17/0.66  fof(f480,plain,(
% 2.17/0.66    ~spl9_2 | ~spl9_3 | ~spl9_1 | spl9_30 | ~spl9_1 | ~spl9_14),
% 2.17/0.66    inference(avatar_split_clause,[],[f476,f197,f120,f478,f120,f130,f125])).
% 2.17/0.66  fof(f476,plain,(
% 2.17/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0)) ) | (~spl9_1 | ~spl9_14)),
% 2.17/0.66    inference(duplicate_literal_removal,[],[f475])).
% 2.17/0.66  fof(f475,plain,(
% 2.17/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0)) ) | (~spl9_1 | ~spl9_14)),
% 2.17/0.66    inference(forward_demodulation,[],[f474,f199])).
% 2.17/0.66  fof(f474,plain,(
% 2.17/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0 | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0)) ) | (~spl9_1 | ~spl9_14)),
% 2.17/0.66    inference(resolution,[],[f472,f84])).
% 2.17/0.66  fof(f84,plain,(
% 2.17/0.66    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f44])).
% 2.17/0.66  fof(f44,plain,(
% 2.17/0.66    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.17/0.66    inference(flattening,[],[f43])).
% 2.17/0.66  fof(f43,plain,(
% 2.17/0.66    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.17/0.66    inference(ennf_transformation,[],[f26])).
% 2.17/0.66  fof(f26,axiom,(
% 2.17/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).
% 2.17/0.66  fof(f472,plain,(
% 2.17/0.66    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl9_1 | ~spl9_14)),
% 2.17/0.66    inference(forward_demodulation,[],[f470,f199])).
% 2.17/0.66  fof(f470,plain,(
% 2.17/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) ) | ~spl9_1),
% 2.17/0.66    inference(resolution,[],[f79,f122])).
% 2.17/0.66  fof(f122,plain,(
% 2.17/0.66    l1_pre_topc(sK0) | ~spl9_1),
% 2.17/0.66    inference(avatar_component_clause,[],[f120])).
% 2.17/0.66  fof(f79,plain,(
% 2.17/0.66    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.17/0.66    inference(cnf_transformation,[],[f39])).
% 2.17/0.66  fof(f39,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.66    inference(flattening,[],[f38])).
% 2.17/0.66  fof(f38,plain,(
% 2.17/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f21])).
% 2.17/0.66  fof(f21,axiom,(
% 2.17/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.17/0.66  fof(f324,plain,(
% 2.17/0.66    spl9_25),
% 2.17/0.66    inference(avatar_contradiction_clause,[],[f320])).
% 2.17/0.66  fof(f320,plain,(
% 2.17/0.66    $false | spl9_25),
% 2.17/0.66    inference(unit_resulting_resolution,[],[f251,f318])).
% 2.17/0.66  fof(f318,plain,(
% 2.17/0.66    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | spl9_25),
% 2.17/0.66    inference(avatar_component_clause,[],[f316])).
% 2.17/0.66  fof(f316,plain,(
% 2.17/0.66    spl9_25 <=> v4_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 2.17/0.66  fof(f251,plain,(
% 2.17/0.66    ( ! [X2] : (v4_relat_1(k1_xboole_0,X2)) )),
% 2.17/0.66    inference(superposition,[],[f107,f246])).
% 2.17/0.66  fof(f246,plain,(
% 2.17/0.66    ( ! [X0] : (k1_xboole_0 = sK8(X0,k1_xboole_0)) )),
% 2.17/0.66    inference(resolution,[],[f245,f80])).
% 2.17/0.66  fof(f245,plain,(
% 2.17/0.66    ( ! [X0] : (r1_tarski(sK8(X0,k1_xboole_0),k1_xboole_0)) )),
% 2.17/0.66    inference(resolution,[],[f243,f100])).
% 2.17/0.66  fof(f100,plain,(
% 2.17/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f10])).
% 2.17/0.66  fof(f243,plain,(
% 2.17/0.66    ( ! [X0] : (m1_subset_1(sK8(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 2.17/0.66    inference(superposition,[],[f105,f117])).
% 2.17/0.66  fof(f105,plain,(
% 2.17/0.66    ( ! [X0,X1] : (m1_subset_1(sK8(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f29])).
% 2.17/0.66  fof(f29,plain,(
% 2.17/0.66    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.66    inference(pure_predicate_removal,[],[f18])).
% 2.17/0.66  fof(f18,axiom,(
% 2.17/0.66    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 2.17/0.66  fof(f107,plain,(
% 2.17/0.66    ( ! [X0,X1] : (v4_relat_1(sK8(X0,X1),X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f29])).
% 2.17/0.66  fof(f319,plain,(
% 2.17/0.66    spl9_24 | ~spl9_25 | ~spl9_13),
% 2.17/0.66    inference(avatar_split_clause,[],[f310,f185,f316,f312])).
% 2.17/0.66  fof(f185,plain,(
% 2.17/0.66    spl9_13 <=> v1_relat_1(k1_xboole_0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 2.17/0.66  fof(f310,plain,(
% 2.17/0.66    ~v4_relat_1(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl9_13),
% 2.17/0.66    inference(resolution,[],[f266,f187])).
% 2.17/0.66  fof(f187,plain,(
% 2.17/0.66    v1_relat_1(k1_xboole_0) | ~spl9_13),
% 2.17/0.66    inference(avatar_component_clause,[],[f185])).
% 2.17/0.66  fof(f266,plain,(
% 2.17/0.66    ( ! [X0] : (~v1_relat_1(X0) | ~v4_relat_1(X0,k1_xboole_0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 2.17/0.66    inference(resolution,[],[f94,f80])).
% 2.17/0.66  fof(f94,plain,(
% 2.17/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f47])).
% 2.17/0.66  fof(f47,plain,(
% 2.17/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.17/0.66    inference(ennf_transformation,[],[f12])).
% 2.17/0.66  fof(f12,axiom,(
% 2.17/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.17/0.66  fof(f259,plain,(
% 2.17/0.66    spl9_21),
% 2.17/0.66    inference(avatar_split_clause,[],[f252,f256])).
% 2.17/0.66  fof(f252,plain,(
% 2.17/0.66    v1_funct_1(k1_xboole_0)),
% 2.17/0.66    inference(superposition,[],[f108,f246])).
% 2.17/0.66  fof(f108,plain,(
% 2.17/0.66    ( ! [X0,X1] : (v1_funct_1(sK8(X0,X1))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f29])).
% 2.17/0.66  fof(f237,plain,(
% 2.17/0.66    spl9_20 | ~spl9_19),
% 2.17/0.66    inference(avatar_split_clause,[],[f232,f226,f234])).
% 2.17/0.66  fof(f232,plain,(
% 2.17/0.66    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | ~spl9_19),
% 2.17/0.66    inference(resolution,[],[f100,f228])).
% 2.17/0.66  fof(f228,plain,(
% 2.17/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl9_19),
% 2.17/0.66    inference(avatar_component_clause,[],[f226])).
% 2.17/0.66  fof(f229,plain,(
% 2.17/0.66    spl9_19 | ~spl9_14 | ~spl9_16),
% 2.17/0.66    inference(avatar_split_clause,[],[f224,f209,f197,f226])).
% 2.17/0.66  fof(f209,plain,(
% 2.17/0.66    spl9_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 2.17/0.66  fof(f224,plain,(
% 2.17/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl9_14 | ~spl9_16)),
% 2.17/0.66    inference(forward_demodulation,[],[f211,f199])).
% 2.17/0.66  fof(f211,plain,(
% 2.17/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl9_16),
% 2.17/0.66    inference(avatar_component_clause,[],[f209])).
% 2.17/0.66  fof(f223,plain,(
% 2.17/0.66    spl9_18 | ~spl9_14 | ~spl9_17),
% 2.17/0.66    inference(avatar_split_clause,[],[f218,f214,f197,f220])).
% 2.17/0.66  fof(f214,plain,(
% 2.17/0.66    spl9_17 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 2.17/0.66  fof(f218,plain,(
% 2.17/0.66    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl9_14 | ~spl9_17)),
% 2.17/0.66    inference(forward_demodulation,[],[f216,f199])).
% 2.17/0.66  fof(f216,plain,(
% 2.17/0.66    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl9_17),
% 2.17/0.66    inference(avatar_component_clause,[],[f214])).
% 2.17/0.66  fof(f217,plain,(
% 2.17/0.66    spl9_17 | ~spl9_8 | ~spl9_15),
% 2.17/0.66    inference(avatar_split_clause,[],[f207,f202,f155,f214])).
% 2.17/0.66  fof(f155,plain,(
% 2.17/0.66    spl9_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 2.17/0.66  fof(f207,plain,(
% 2.17/0.66    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl9_8 | ~spl9_15)),
% 2.17/0.66    inference(backward_demodulation,[],[f157,f204])).
% 2.17/0.66  fof(f157,plain,(
% 2.17/0.66    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl9_8),
% 2.17/0.66    inference(avatar_component_clause,[],[f155])).
% 2.17/0.66  fof(f212,plain,(
% 2.17/0.66    spl9_16 | ~spl9_7 | ~spl9_15),
% 2.17/0.66    inference(avatar_split_clause,[],[f206,f202,f150,f209])).
% 2.17/0.66  fof(f150,plain,(
% 2.17/0.66    spl9_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 2.17/0.66  fof(f206,plain,(
% 2.17/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl9_7 | ~spl9_15)),
% 2.17/0.66    inference(backward_demodulation,[],[f152,f204])).
% 2.17/0.66  fof(f152,plain,(
% 2.17/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl9_7),
% 2.17/0.66    inference(avatar_component_clause,[],[f150])).
% 2.17/0.66  fof(f205,plain,(
% 2.17/0.66    spl9_15 | ~spl9_12),
% 2.17/0.66    inference(avatar_split_clause,[],[f195,f178,f202])).
% 2.17/0.66  fof(f178,plain,(
% 2.17/0.66    spl9_12 <=> l1_struct_0(sK1)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 2.17/0.66  fof(f195,plain,(
% 2.17/0.66    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl9_12),
% 2.17/0.66    inference(resolution,[],[f67,f180])).
% 2.17/0.66  fof(f180,plain,(
% 2.17/0.66    l1_struct_0(sK1) | ~spl9_12),
% 2.17/0.66    inference(avatar_component_clause,[],[f178])).
% 2.17/0.66  fof(f67,plain,(
% 2.17/0.66    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f32])).
% 2.17/0.66  fof(f32,plain,(
% 2.17/0.66    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f19])).
% 2.17/0.66  fof(f19,axiom,(
% 2.17/0.66    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.17/0.66  fof(f200,plain,(
% 2.17/0.66    spl9_14 | ~spl9_11),
% 2.17/0.66    inference(avatar_split_clause,[],[f194,f173,f197])).
% 2.17/0.66  fof(f173,plain,(
% 2.17/0.66    spl9_11 <=> l1_struct_0(sK0)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 2.17/0.66  fof(f194,plain,(
% 2.17/0.66    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl9_11),
% 2.17/0.66    inference(resolution,[],[f67,f175])).
% 2.17/0.66  fof(f175,plain,(
% 2.17/0.66    l1_struct_0(sK0) | ~spl9_11),
% 2.17/0.66    inference(avatar_component_clause,[],[f173])).
% 2.17/0.66  fof(f188,plain,(
% 2.17/0.66    spl9_13),
% 2.17/0.66    inference(avatar_split_clause,[],[f183,f185])).
% 2.17/0.66  fof(f183,plain,(
% 2.17/0.66    v1_relat_1(k1_xboole_0)),
% 2.17/0.66    inference(superposition,[],[f92,f117])).
% 2.17/0.66  fof(f92,plain,(
% 2.17/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f13])).
% 2.17/0.66  fof(f13,axiom,(
% 2.17/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.17/0.66  fof(f181,plain,(
% 2.17/0.66    spl9_12 | ~spl9_4),
% 2.17/0.66    inference(avatar_split_clause,[],[f171,f135,f178])).
% 2.17/0.66  fof(f171,plain,(
% 2.17/0.66    l1_struct_0(sK1) | ~spl9_4),
% 2.17/0.66    inference(resolution,[],[f68,f137])).
% 2.17/0.66  fof(f137,plain,(
% 2.17/0.66    l1_pre_topc(sK1) | ~spl9_4),
% 2.17/0.66    inference(avatar_component_clause,[],[f135])).
% 2.17/0.66  fof(f68,plain,(
% 2.17/0.66    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f33])).
% 2.17/0.66  fof(f33,plain,(
% 2.17/0.66    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.17/0.66    inference(ennf_transformation,[],[f20])).
% 2.17/0.66  fof(f20,axiom,(
% 2.17/0.66    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.17/0.66  fof(f176,plain,(
% 2.17/0.66    spl9_11 | ~spl9_1),
% 2.17/0.66    inference(avatar_split_clause,[],[f170,f120,f173])).
% 2.17/0.66  fof(f170,plain,(
% 2.17/0.66    l1_struct_0(sK0) | ~spl9_1),
% 2.17/0.66    inference(resolution,[],[f68,f122])).
% 2.17/0.66  fof(f168,plain,(
% 2.17/0.66    spl9_10),
% 2.17/0.66    inference(avatar_split_clause,[],[f63,f165])).
% 2.17/0.66  fof(f63,plain,(
% 2.17/0.66    v1_xboole_0(k1_xboole_0)),
% 2.17/0.66    inference(cnf_transformation,[],[f2])).
% 2.17/0.66  fof(f2,axiom,(
% 2.17/0.66    v1_xboole_0(k1_xboole_0)),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.17/0.66  fof(f163,plain,(
% 2.17/0.66    spl9_9),
% 2.17/0.66    inference(avatar_split_clause,[],[f54,f160])).
% 2.17/0.66  fof(f54,plain,(
% 2.17/0.66    v1_funct_1(sK2)),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f31,plain,(
% 2.17/0.66    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 2.17/0.66    inference(flattening,[],[f30])).
% 2.17/0.66  fof(f30,plain,(
% 2.17/0.66    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 2.17/0.66    inference(ennf_transformation,[],[f28])).
% 2.17/0.66  fof(f28,negated_conjecture,(
% 2.17/0.66    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.17/0.66    inference(negated_conjecture,[],[f27])).
% 2.17/0.66  fof(f27,conjecture,(
% 2.17/0.66    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).
% 2.17/0.66  fof(f158,plain,(
% 2.17/0.66    spl9_8),
% 2.17/0.66    inference(avatar_split_clause,[],[f55,f155])).
% 2.17/0.66  fof(f55,plain,(
% 2.17/0.66    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f153,plain,(
% 2.17/0.66    spl9_7),
% 2.17/0.66    inference(avatar_split_clause,[],[f56,f150])).
% 2.17/0.66  fof(f56,plain,(
% 2.17/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f148,plain,(
% 2.17/0.66    ~spl9_6),
% 2.17/0.66    inference(avatar_split_clause,[],[f57,f145])).
% 2.17/0.66  fof(f57,plain,(
% 2.17/0.66    ~v5_pre_topc(sK2,sK0,sK1)),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f143,plain,(
% 2.17/0.66    spl9_5),
% 2.17/0.66    inference(avatar_split_clause,[],[f58,f140])).
% 2.17/0.66  fof(f58,plain,(
% 2.17/0.66    v2_pre_topc(sK1)),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f138,plain,(
% 2.17/0.66    spl9_4),
% 2.17/0.66    inference(avatar_split_clause,[],[f59,f135])).
% 2.17/0.66  fof(f59,plain,(
% 2.17/0.66    l1_pre_topc(sK1)),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f133,plain,(
% 2.17/0.66    spl9_3),
% 2.17/0.66    inference(avatar_split_clause,[],[f60,f130])).
% 2.17/0.66  fof(f60,plain,(
% 2.17/0.66    v2_pre_topc(sK0)),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f128,plain,(
% 2.17/0.66    spl9_2),
% 2.17/0.66    inference(avatar_split_clause,[],[f61,f125])).
% 2.17/0.66  fof(f61,plain,(
% 2.17/0.66    v1_tdlat_3(sK0)),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  fof(f123,plain,(
% 2.17/0.66    spl9_1),
% 2.17/0.66    inference(avatar_split_clause,[],[f62,f120])).
% 2.17/0.66  fof(f62,plain,(
% 2.17/0.66    l1_pre_topc(sK0)),
% 2.17/0.66    inference(cnf_transformation,[],[f31])).
% 2.17/0.66  % SZS output end Proof for theBenchmark
% 2.17/0.66  % (19310)------------------------------
% 2.17/0.66  % (19310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (19310)Termination reason: Refutation
% 2.17/0.66  
% 2.17/0.66  % (19310)Memory used [KB]: 7675
% 2.17/0.66  % (19310)Time elapsed: 0.189 s
% 2.17/0.66  % (19310)------------------------------
% 2.17/0.66  % (19310)------------------------------
% 2.17/0.66  % (19294)Success in time 0.296 s
%------------------------------------------------------------------------------
