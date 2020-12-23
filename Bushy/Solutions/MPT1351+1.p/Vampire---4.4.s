%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t76_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:44 EDT 2019

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  544 (1911 expanded)
%              Number of leaves         :  148 ( 757 expanded)
%              Depth                    :   13
%              Number of atoms          : 1562 (6474 expanded)
%              Number of equality atoms :   59 ( 184 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2072,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f142,f149,f156,f163,f170,f177,f184,f191,f198,f205,f215,f222,f229,f236,f243,f250,f261,f270,f277,f284,f291,f315,f325,f332,f341,f350,f366,f384,f394,f412,f419,f440,f451,f487,f505,f518,f544,f551,f575,f591,f601,f635,f645,f652,f665,f673,f680,f687,f689,f745,f820,f827,f840,f858,f871,f896,f912,f920,f930,f938,f945,f952,f958,f1005,f1022,f1095,f1126,f1154,f1165,f1174,f1183,f1190,f1204,f1226,f1233,f1245,f1252,f1262,f1271,f1278,f1320,f1322,f1344,f1423,f1452,f1499,f1511,f1520,f1557,f1594,f1596,f1612,f1746,f1764,f1772,f1779,f1795,f1802,f1809,f1816,f1823,f1830,f1872,f1879,f1886,f1893,f1900,f1915,f1946,f1969,f1989,f1998,f2005,f2012,f2019,f2046,f2071])).

fof(f2071,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_32
    | spl7_87
    | ~ spl7_106
    | ~ spl7_138
    | ~ spl7_154
    | ~ spl7_160
    | ~ spl7_184
    | ~ spl7_218 ),
    inference(avatar_contradiction_clause,[],[f2070])).

fof(f2070,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_32
    | ~ spl7_87
    | ~ spl7_106
    | ~ spl7_138
    | ~ spl7_154
    | ~ spl7_160
    | ~ spl7_184
    | ~ spl7_218 ),
    inference(subsumption_resolution,[],[f2069,f634])).

fof(f634,plain,
    ( ~ v2_connsp_1(k10_relat_1(sK2,sK3),sK0)
    | ~ spl7_87 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl7_87
  <=> ~ v2_connsp_1(k10_relat_1(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f2069,plain,
    ( v2_connsp_1(k10_relat_1(sK2,sK3),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_32
    | ~ spl7_106
    | ~ spl7_138
    | ~ spl7_154
    | ~ spl7_160
    | ~ spl7_184
    | ~ spl7_218 ),
    inference(forward_demodulation,[],[f2047,f1405])).

fof(f1405,plain,
    ( k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) = k10_relat_1(sK2,sK3)
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_32
    | ~ spl7_106
    | ~ spl7_154 ),
    inference(forward_demodulation,[],[f1395,f607])).

fof(f607,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f249,f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',redefinition_k8_relset_1)).

fof(f249,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f1395,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | ~ spl7_12
    | ~ spl7_22
    | ~ spl7_24
    | ~ spl7_28
    | ~ spl7_30
    | ~ spl7_32
    | ~ spl7_106
    | ~ spl7_154 ),
    inference(unit_resulting_resolution,[],[f214,f221,f176,f839,f235,f242,f249,f1261,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v2_funct_1(X2)
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t68_tops_2)).

fof(f1261,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_154 ),
    inference(avatar_component_clause,[],[f1260])).

fof(f1260,plain,
    ( spl7_154
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f242,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl7_30
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f235,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl7_28
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f839,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl7_106
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f176,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl7_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f221,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl7_24
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f214,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_22
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f2047,plain,
    ( v2_connsp_1(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_28
    | ~ spl7_138
    | ~ spl7_160
    | ~ spl7_184
    | ~ spl7_218 ),
    inference(unit_resulting_resolution,[],[f155,f162,f169,f134,f141,f148,f197,f235,f1182,f1343,f1794,f2011,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
      | ~ v2_connsp_1(X3,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v2_connsp_1(X3,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v2_connsp_1(X3,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_connsp_1(X3,X0)
                      & v5_pre_topc(X2,X0,X1) )
                   => v2_connsp_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t75_tops_2)).

fof(f2011,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_218 ),
    inference(avatar_component_clause,[],[f2010])).

fof(f2010,plain,
    ( spl7_218
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f1794,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_184 ),
    inference(avatar_component_clause,[],[f1793])).

fof(f1793,plain,
    ( spl7_184
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).

fof(f1343,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl7_160 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1342,plain,
    ( spl7_160
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f1182,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl7_138 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1181,plain,
    ( spl7_138
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f197,plain,
    ( v2_connsp_1(sK3,sK1)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl7_18
  <=> v2_connsp_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f148,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f141,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f134,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f169,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f162,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_8
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f155,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f2046,plain,
    ( ~ spl7_223
    | spl7_201 ),
    inference(avatar_split_clause,[],[f1923,f1884,f2044])).

fof(f2044,plain,
    ( spl7_223
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(sK4(sK4(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_223])])).

fof(f1884,plain,
    ( spl7_201
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK4(sK4(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_201])])).

fof(f1923,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_zfmisc_1(sK4(sK4(sK3)))))
    | ~ spl7_201 ),
    inference(unit_resulting_resolution,[],[f1885,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t1_subset)).

fof(f1885,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK4(sK4(sK3)))))
    | ~ spl7_201 ),
    inference(avatar_component_clause,[],[f1884])).

fof(f2019,plain,
    ( spl7_220
    | spl7_209 ),
    inference(avatar_split_clause,[],[f1959,f1941,f2017])).

fof(f2017,plain,
    ( spl7_220
  <=> r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_220])])).

fof(f1941,plain,
    ( spl7_209
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_209])])).

fof(f1959,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_209 ),
    inference(unit_resulting_resolution,[],[f108,f1942,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t2_subset)).

fof(f1942,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_209 ),
    inference(avatar_component_clause,[],[f1941])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',existence_m1_subset_1)).

fof(f2012,plain,
    ( spl7_218
    | ~ spl7_12
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f808,f248,f241,f175,f2010])).

fof(f808,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl7_12
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f176,f242,f249,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',dt_k2_tops_2)).

fof(f2005,plain,
    ( ~ spl7_217
    | spl7_209 ),
    inference(avatar_split_clause,[],[f1954,f1941,f2003])).

fof(f2003,plain,
    ( spl7_217
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_217])])).

fof(f1954,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_209 ),
    inference(unit_resulting_resolution,[],[f108,f1942,f263])).

fof(f263,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f111,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',antisymmetry_r2_hidden)).

fof(f1998,plain,
    ( ~ spl7_215
    | spl7_85
    | spl7_209 ),
    inference(avatar_split_clause,[],[f1949,f1941,f596,f1996])).

fof(f1996,plain,
    ( spl7_215
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_215])])).

fof(f596,plain,
    ( spl7_85
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f1949,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_85
    | ~ spl7_209 ),
    inference(unit_resulting_resolution,[],[f597,f108,f1942,f292])).

fof(f292,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f263,f111])).

fof(f597,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_85 ),
    inference(avatar_component_clause,[],[f596])).

fof(f1989,plain,
    ( ~ spl7_213
    | spl7_211 ),
    inference(avatar_split_clause,[],[f1981,f1967,f1987])).

fof(f1987,plain,
    ( spl7_213
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_213])])).

fof(f1967,plain,
    ( spl7_211
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_211])])).

fof(f1981,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_211 ),
    inference(unit_resulting_resolution,[],[f1968,f110])).

fof(f1968,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_211 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f1969,plain,
    ( ~ spl7_211
    | spl7_209 ),
    inference(avatar_split_clause,[],[f1947,f1941,f1967])).

fof(f1947,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_209 ),
    inference(unit_resulting_resolution,[],[f1942,f298])).

fof(f298,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f292])).

fof(f1946,plain,
    ( ~ spl7_129
    | spl7_208
    | spl7_131 ),
    inference(avatar_split_clause,[],[f1127,f1124,f1944,f1090])).

fof(f1090,plain,
    ( spl7_129
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f1944,plain,
    ( spl7_208
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_208])])).

fof(f1124,plain,
    ( spl7_131
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_131])])).

fof(f1127,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_131 ),
    inference(resolution,[],[f1125,f111])).

fof(f1125,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_131 ),
    inference(avatar_component_clause,[],[f1124])).

fof(f1915,plain,
    ( ~ spl7_207
    | spl7_193 ),
    inference(avatar_split_clause,[],[f1854,f1821,f1913])).

fof(f1913,plain,
    ( spl7_207
  <=> ~ r2_hidden(sK4(k1_xboole_0),k1_zfmisc_1(sK4(sK4(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_207])])).

fof(f1821,plain,
    ( spl7_193
  <=> ~ m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(sK4(sK4(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_193])])).

fof(f1854,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0),k1_zfmisc_1(sK4(sK4(k1_xboole_0))))
    | ~ spl7_193 ),
    inference(unit_resulting_resolution,[],[f1822,f110])).

fof(f1822,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(sK4(sK4(k1_xboole_0))))
    | ~ spl7_193 ),
    inference(avatar_component_clause,[],[f1821])).

fof(f1900,plain,
    ( ~ spl7_205
    | ~ spl7_78
    | spl7_193 ),
    inference(avatar_split_clause,[],[f1848,f1821,f549,f1898])).

fof(f1898,plain,
    ( spl7_205
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4(sK4(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_205])])).

fof(f549,plain,
    ( spl7_78
  <=> r2_hidden(sK4(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f1848,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK4(sK4(k1_xboole_0)))))
    | ~ spl7_78
    | ~ spl7_193 ),
    inference(unit_resulting_resolution,[],[f550,f1822,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t4_subset)).

fof(f550,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f549])).

fof(f1893,plain,
    ( ~ spl7_203
    | spl7_191 ),
    inference(avatar_split_clause,[],[f1846,f1814,f1891])).

fof(f1891,plain,
    ( spl7_203
  <=> ~ r2_hidden(sK4(sK3),k1_zfmisc_1(sK4(sK4(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_203])])).

fof(f1814,plain,
    ( spl7_191
  <=> ~ m1_subset_1(sK4(sK3),k1_zfmisc_1(sK4(sK4(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_191])])).

fof(f1846,plain,
    ( ~ r2_hidden(sK4(sK3),k1_zfmisc_1(sK4(sK4(sK3))))
    | ~ spl7_191 ),
    inference(unit_resulting_resolution,[],[f1815,f110])).

fof(f1815,plain,
    ( ~ m1_subset_1(sK4(sK3),k1_zfmisc_1(sK4(sK4(sK3))))
    | ~ spl7_191 ),
    inference(avatar_component_clause,[],[f1814])).

fof(f1886,plain,
    ( ~ spl7_201
    | ~ spl7_64
    | spl7_191 ),
    inference(avatar_split_clause,[],[f1839,f1814,f417,f1884])).

fof(f417,plain,
    ( spl7_64
  <=> r2_hidden(sK4(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f1839,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK4(sK4(sK3)))))
    | ~ spl7_64
    | ~ spl7_191 ),
    inference(unit_resulting_resolution,[],[f418,f1815,f121])).

fof(f418,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f417])).

fof(f1879,plain,
    ( ~ spl7_199
    | spl7_189 ),
    inference(avatar_split_clause,[],[f1837,f1807,f1877])).

fof(f1877,plain,
    ( spl7_199
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK4(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_199])])).

fof(f1807,plain,
    ( spl7_189
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_189])])).

fof(f1837,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK4(u1_struct_0(sK1))))
    | ~ spl7_189 ),
    inference(unit_resulting_resolution,[],[f1808,f110])).

fof(f1808,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(u1_struct_0(sK1))))
    | ~ spl7_189 ),
    inference(avatar_component_clause,[],[f1807])).

fof(f1872,plain,
    ( ~ spl7_197
    | spl7_151 ),
    inference(avatar_split_clause,[],[f1253,f1243,f1870])).

fof(f1870,plain,
    ( spl7_197
  <=> ~ r2_hidden(u1_struct_0(sK1),sK4(k1_zfmisc_1(sK4(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_197])])).

fof(f1243,plain,
    ( spl7_151
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).

fof(f1253,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(k1_zfmisc_1(sK4(sK3))))
    | ~ spl7_151 ),
    inference(unit_resulting_resolution,[],[f108,f1244,f121])).

fof(f1244,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK4(sK3))
    | ~ spl7_151 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f1830,plain,
    ( ~ spl7_195
    | spl7_183 ),
    inference(avatar_split_clause,[],[f1787,f1777,f1828])).

fof(f1828,plain,
    ( spl7_195
  <=> ~ r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_195])])).

fof(f1777,plain,
    ( spl7_183
  <=> ~ m1_subset_1(sK4(k1_zfmisc_1(k1_xboole_0)),sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_183])])).

fof(f1787,plain,
    ( ~ r2_hidden(sK4(k1_zfmisc_1(k1_xboole_0)),sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_183 ),
    inference(unit_resulting_resolution,[],[f1778,f110])).

fof(f1778,plain,
    ( ~ m1_subset_1(sK4(k1_zfmisc_1(k1_xboole_0)),sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_183 ),
    inference(avatar_component_clause,[],[f1777])).

fof(f1823,plain,
    ( ~ spl7_193
    | ~ spl7_174 ),
    inference(avatar_split_clause,[],[f1752,f1555,f1821])).

fof(f1555,plain,
    ( spl7_174
  <=> r2_hidden(sK4(sK4(k1_xboole_0)),sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f1752,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0),k1_zfmisc_1(sK4(sK4(k1_xboole_0))))
    | ~ spl7_174 ),
    inference(unit_resulting_resolution,[],[f1556,f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f299,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t5_subset)).

fof(f299,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f298,f121])).

fof(f1556,plain,
    ( r2_hidden(sK4(sK4(k1_xboole_0)),sK4(k1_xboole_0))
    | ~ spl7_174 ),
    inference(avatar_component_clause,[],[f1555])).

fof(f1816,plain,
    ( ~ spl7_191
    | ~ spl7_158 ),
    inference(avatar_split_clause,[],[f1429,f1276,f1814])).

fof(f1276,plain,
    ( spl7_158
  <=> r2_hidden(sK4(sK4(sK3)),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f1429,plain,
    ( ~ m1_subset_1(sK4(sK3),k1_zfmisc_1(sK4(sK4(sK3))))
    | ~ spl7_158 ),
    inference(unit_resulting_resolution,[],[f1277,f300])).

fof(f1277,plain,
    ( r2_hidden(sK4(sK4(sK3)),sK4(sK3))
    | ~ spl7_158 ),
    inference(avatar_component_clause,[],[f1276])).

fof(f1809,plain,
    ( ~ spl7_189
    | ~ spl7_124 ),
    inference(avatar_split_clause,[],[f1143,f950,f1807])).

fof(f950,plain,
    ( spl7_124
  <=> r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f1143,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(u1_struct_0(sK1))))
    | ~ spl7_124 ),
    inference(unit_resulting_resolution,[],[f951,f300])).

fof(f951,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_124 ),
    inference(avatar_component_clause,[],[f950])).

fof(f1802,plain,
    ( ~ spl7_187
    | spl7_95 ),
    inference(avatar_split_clause,[],[f897,f671,f1800])).

fof(f1800,plain,
    ( spl7_187
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_187])])).

fof(f671,plain,
    ( spl7_95
  <=> ~ m1_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f897,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl7_95 ),
    inference(unit_resulting_resolution,[],[f108,f672,f121])).

fof(f672,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f671])).

fof(f1795,plain,
    ( spl7_184
    | ~ spl7_12
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f666,f248,f241,f175,f1793])).

fof(f666,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_12
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f176,f242,f249,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1779,plain,
    ( ~ spl7_183
    | spl7_85 ),
    inference(avatar_split_clause,[],[f1668,f596,f1777])).

fof(f1668,plain,
    ( ~ m1_subset_1(sK4(k1_zfmisc_1(k1_xboole_0)),sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_85 ),
    inference(unit_resulting_resolution,[],[f597,f298])).

fof(f1772,plain,
    ( ~ spl7_181
    | spl7_91 ),
    inference(avatar_split_clause,[],[f656,f650,f1770])).

fof(f1770,plain,
    ( spl7_181
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_181])])).

fof(f650,plain,
    ( spl7_91
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f656,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(k1_xboole_0)))))
    | ~ spl7_91 ),
    inference(unit_resulting_resolution,[],[f108,f651,f121])).

fof(f651,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4(k1_xboole_0)))
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f650])).

fof(f1764,plain,
    ( ~ spl7_179
    | spl7_89 ),
    inference(avatar_split_clause,[],[f653,f643,f1762])).

fof(f1762,plain,
    ( spl7_179
  <=> ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_179])])).

fof(f643,plain,
    ( spl7_89
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f653,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(sK4(sK3)))))
    | ~ spl7_89 ),
    inference(unit_resulting_resolution,[],[f108,f644,f121])).

fof(f644,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4(sK3)))
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f643])).

fof(f1746,plain,
    ( ~ spl7_177
    | spl7_165 ),
    inference(avatar_split_clause,[],[f1461,f1444,f1744])).

fof(f1744,plain,
    ( spl7_177
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(sK4(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_177])])).

fof(f1444,plain,
    ( spl7_165
  <=> ~ m1_subset_1(k1_xboole_0,sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_165])])).

fof(f1461,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(sK4(k1_xboole_0))))
    | ~ spl7_165 ),
    inference(unit_resulting_resolution,[],[f108,f1445,f121])).

fof(f1445,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK4(k1_xboole_0))
    | ~ spl7_165 ),
    inference(avatar_component_clause,[],[f1444])).

fof(f1612,plain,
    ( spl7_91
    | ~ spl7_128
    | ~ spl7_166 ),
    inference(avatar_contradiction_clause,[],[f1611])).

fof(f1611,plain,
    ( $false
    | ~ spl7_91
    | ~ spl7_128
    | ~ spl7_166 ),
    inference(subsumption_resolution,[],[f1094,f1576])).

fof(f1576,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_91
    | ~ spl7_166 ),
    inference(backward_demodulation,[],[f1569,f651])).

fof(f1569,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0)
    | ~ spl7_166 ),
    inference(unit_resulting_resolution,[],[f1451,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t6_boole)).

fof(f1451,plain,
    ( v1_xboole_0(sK4(k1_xboole_0))
    | ~ spl7_166 ),
    inference(avatar_component_clause,[],[f1450])).

fof(f1450,plain,
    ( spl7_166
  <=> v1_xboole_0(sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f1094,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_128 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1093,plain,
    ( spl7_128
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f1596,plain,
    ( spl7_71
    | ~ spl7_166 ),
    inference(avatar_contradiction_clause,[],[f1595])).

fof(f1595,plain,
    ( $false
    | ~ spl7_71
    | ~ spl7_166 ),
    inference(subsumption_resolution,[],[f1581,f483])).

fof(f483,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl7_71
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f1581,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_166 ),
    inference(backward_demodulation,[],[f1569,f1451])).

fof(f1594,plain,
    ( spl7_75
    | ~ spl7_78
    | ~ spl7_166 ),
    inference(avatar_contradiction_clause,[],[f1593])).

fof(f1593,plain,
    ( $false
    | ~ spl7_75
    | ~ spl7_78
    | ~ spl7_166 ),
    inference(subsumption_resolution,[],[f1575,f517])).

fof(f517,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f516])).

fof(f516,plain,
    ( spl7_75
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f1575,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_78
    | ~ spl7_166 ),
    inference(backward_demodulation,[],[f1569,f550])).

fof(f1557,plain,
    ( spl7_174
    | spl7_167 ),
    inference(avatar_split_clause,[],[f1458,f1447,f1555])).

fof(f1447,plain,
    ( spl7_167
  <=> ~ v1_xboole_0(sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_167])])).

fof(f1458,plain,
    ( r2_hidden(sK4(sK4(k1_xboole_0)),sK4(k1_xboole_0))
    | ~ spl7_167 ),
    inference(unit_resulting_resolution,[],[f108,f1448,f111])).

fof(f1448,plain,
    ( ~ v1_xboole_0(sK4(k1_xboole_0))
    | ~ spl7_167 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f1520,plain,
    ( ~ spl7_173
    | spl7_167 ),
    inference(avatar_split_clause,[],[f1457,f1447,f1518])).

fof(f1518,plain,
    ( spl7_173
  <=> ~ r2_hidden(sK4(k1_xboole_0),sK4(sK4(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_173])])).

fof(f1457,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0),sK4(sK4(k1_xboole_0)))
    | ~ spl7_167 ),
    inference(unit_resulting_resolution,[],[f108,f1448,f263])).

fof(f1511,plain,
    ( ~ spl7_171
    | spl7_169 ),
    inference(avatar_split_clause,[],[f1503,f1497,f1509])).

fof(f1509,plain,
    ( spl7_171
  <=> ~ r2_hidden(sK4(k1_xboole_0),sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).

fof(f1497,plain,
    ( spl7_169
  <=> ~ m1_subset_1(sK4(k1_xboole_0),sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_169])])).

fof(f1503,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0),sK4(k1_xboole_0))
    | ~ spl7_169 ),
    inference(unit_resulting_resolution,[],[f1498,f110])).

fof(f1498,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0),sK4(k1_xboole_0))
    | ~ spl7_169 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f1499,plain,
    ( ~ spl7_169
    | spl7_167 ),
    inference(avatar_split_clause,[],[f1453,f1447,f1497])).

fof(f1453,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0),sK4(k1_xboole_0))
    | ~ spl7_167 ),
    inference(unit_resulting_resolution,[],[f1448,f298])).

fof(f1452,plain,
    ( ~ spl7_165
    | spl7_166
    | spl7_77 ),
    inference(avatar_split_clause,[],[f566,f542,f1450,f1444])).

fof(f542,plain,
    ( spl7_77
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f566,plain,
    ( v1_xboole_0(sK4(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK4(k1_xboole_0))
    | ~ spl7_77 ),
    inference(resolution,[],[f543,f111])).

fof(f543,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0))
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f542])).

fof(f1423,plain,
    ( ~ spl7_163
    | spl7_143 ),
    inference(avatar_split_clause,[],[f1217,f1196,f1421])).

fof(f1421,plain,
    ( spl7_163
  <=> ~ r2_hidden(sK3,sK4(k1_zfmisc_1(sK4(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_163])])).

fof(f1196,plain,
    ( spl7_143
  <=> ~ m1_subset_1(sK3,sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_143])])).

fof(f1217,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(sK4(sK3))))
    | ~ spl7_143 ),
    inference(unit_resulting_resolution,[],[f108,f1197,f121])).

fof(f1197,plain,
    ( ~ m1_subset_1(sK3,sK4(sK3))
    | ~ spl7_143 ),
    inference(avatar_component_clause,[],[f1196])).

fof(f1344,plain,
    ( spl7_160
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f923,f248,f241,f203,f175,f168,f147,f1342])).

fof(f203,plain,
    ( spl7_20
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f923,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f148,f169,f176,f204,f242,f249,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',d5_tops_2)).

fof(f204,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f203])).

fof(f1322,plain,
    ( ~ spl7_78
    | ~ spl7_144
    | spl7_159 ),
    inference(avatar_contradiction_clause,[],[f1321])).

fof(f1321,plain,
    ( $false
    | ~ spl7_78
    | ~ spl7_144
    | ~ spl7_159 ),
    inference(subsumption_resolution,[],[f1316,f550])).

fof(f1316,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl7_144
    | ~ spl7_159 ),
    inference(backward_demodulation,[],[f1287,f1274])).

fof(f1274,plain,
    ( ~ r2_hidden(sK4(sK4(sK3)),sK4(sK3))
    | ~ spl7_159 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f1273,plain,
    ( spl7_159
  <=> ~ r2_hidden(sK4(sK4(sK3)),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_159])])).

fof(f1287,plain,
    ( k1_xboole_0 = sK4(sK3)
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f1203,f97])).

fof(f1203,plain,
    ( v1_xboole_0(sK4(sK3))
    | ~ spl7_144 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f1202,plain,
    ( spl7_144
  <=> v1_xboole_0(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f1320,plain,
    ( spl7_71
    | ~ spl7_144 ),
    inference(avatar_contradiction_clause,[],[f1319])).

fof(f1319,plain,
    ( $false
    | ~ spl7_71
    | ~ spl7_144 ),
    inference(subsumption_resolution,[],[f1307,f483])).

fof(f1307,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_144 ),
    inference(backward_demodulation,[],[f1287,f1203])).

fof(f1278,plain,
    ( spl7_158
    | spl7_145 ),
    inference(avatar_split_clause,[],[f1213,f1199,f1276])).

fof(f1199,plain,
    ( spl7_145
  <=> ~ v1_xboole_0(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f1213,plain,
    ( r2_hidden(sK4(sK4(sK3)),sK4(sK3))
    | ~ spl7_145 ),
    inference(unit_resulting_resolution,[],[f108,f1200,f111])).

fof(f1200,plain,
    ( ~ v1_xboole_0(sK4(sK3))
    | ~ spl7_145 ),
    inference(avatar_component_clause,[],[f1199])).

fof(f1271,plain,
    ( ~ spl7_157
    | spl7_145 ),
    inference(avatar_split_clause,[],[f1212,f1199,f1269])).

fof(f1269,plain,
    ( spl7_157
  <=> ~ r2_hidden(sK4(sK3),sK4(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_157])])).

fof(f1212,plain,
    ( ~ r2_hidden(sK4(sK3),sK4(sK4(sK3)))
    | ~ spl7_145 ),
    inference(unit_resulting_resolution,[],[f108,f1200,f263])).

fof(f1262,plain,
    ( spl7_154
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f902,f248,f241,f203,f175,f168,f147,f1260])).

fof(f902,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f148,f169,f176,f204,f242,f249,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f1252,plain,
    ( ~ spl7_153
    | spl7_149 ),
    inference(avatar_split_clause,[],[f1237,f1231,f1250])).

fof(f1250,plain,
    ( spl7_153
  <=> ~ r2_hidden(sK4(sK3),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_153])])).

fof(f1231,plain,
    ( spl7_149
  <=> ~ m1_subset_1(sK4(sK3),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_149])])).

fof(f1237,plain,
    ( ~ r2_hidden(sK4(sK3),sK4(sK3))
    | ~ spl7_149 ),
    inference(unit_resulting_resolution,[],[f1232,f110])).

fof(f1232,plain,
    ( ~ m1_subset_1(sK4(sK3),sK4(sK3))
    | ~ spl7_149 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1245,plain,
    ( ~ spl7_151
    | spl7_97
    | spl7_145 ),
    inference(avatar_split_clause,[],[f1214,f1199,f678,f1243])).

fof(f678,plain,
    ( spl7_97
  <=> ~ r2_hidden(u1_struct_0(sK1),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f1214,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK4(sK3))
    | ~ spl7_97
    | ~ spl7_145 ),
    inference(unit_resulting_resolution,[],[f679,f1200,f111])).

fof(f679,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(sK3))
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f678])).

fof(f1233,plain,
    ( ~ spl7_149
    | spl7_145 ),
    inference(avatar_split_clause,[],[f1205,f1199,f1231])).

fof(f1205,plain,
    ( ~ m1_subset_1(sK4(sK3),sK4(sK3))
    | ~ spl7_145 ),
    inference(unit_resulting_resolution,[],[f1200,f298])).

fof(f1226,plain,
    ( spl7_146
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f886,f248,f241,f203,f175,f168,f147,f1224])).

fof(f1224,plain,
    ( spl7_146
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f886,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f148,f169,f176,f204,f242,f249,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f1204,plain,
    ( ~ spl7_143
    | spl7_144
    | spl7_63 ),
    inference(avatar_split_clause,[],[f420,f410,f1202,f1196])).

fof(f410,plain,
    ( spl7_63
  <=> ~ r2_hidden(sK3,sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f420,plain,
    ( v1_xboole_0(sK4(sK3))
    | ~ m1_subset_1(sK3,sK4(sK3))
    | ~ spl7_63 ),
    inference(resolution,[],[f411,f111])).

fof(f411,plain,
    ( ~ r2_hidden(sK3,sK4(sK3))
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f410])).

fof(f1190,plain,
    ( ~ spl7_141
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f305,f248,f1188])).

fof(f1188,plain,
    ( spl7_141
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_141])])).

fof(f305,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f249,f300])).

fof(f1183,plain,
    ( spl7_138
    | ~ spl7_12
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f638,f248,f241,f175,f1181])).

fof(f638,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl7_12
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f176,f242,f249,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1174,plain,
    ( ~ spl7_137
    | spl7_133 ),
    inference(avatar_split_clause,[],[f1157,f1152,f1172])).

fof(f1172,plain,
    ( spl7_137
  <=> ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).

fof(f1152,plain,
    ( spl7_133
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_133])])).

fof(f1157,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK3)))
    | ~ spl7_133 ),
    inference(unit_resulting_resolution,[],[f1153,f110])).

fof(f1153,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK3)))
    | ~ spl7_133 ),
    inference(avatar_component_clause,[],[f1152])).

fof(f1165,plain,
    ( ~ spl7_135
    | spl7_129 ),
    inference(avatar_split_clause,[],[f1117,f1090,f1163])).

fof(f1163,plain,
    ( spl7_135
  <=> ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_135])])).

fof(f1117,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_129 ),
    inference(unit_resulting_resolution,[],[f108,f1091,f121])).

fof(f1091,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_129 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1154,plain,
    ( ~ spl7_133
    | ~ spl7_98 ),
    inference(avatar_split_clause,[],[f1081,f685,f1152])).

fof(f685,plain,
    ( spl7_98
  <=> r2_hidden(sK4(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f1081,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK3)))
    | ~ spl7_98 ),
    inference(unit_resulting_resolution,[],[f686,f300])).

fof(f686,plain,
    ( r2_hidden(sK4(sK3),u1_struct_0(sK1))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f685])).

fof(f1126,plain,
    ( ~ spl7_131
    | spl7_129 ),
    inference(avatar_split_clause,[],[f1118,f1090,f1124])).

fof(f1118,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_129 ),
    inference(unit_resulting_resolution,[],[f1091,f110])).

fof(f1095,plain,
    ( spl7_128
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f1088,f856,f1093])).

fof(f856,plain,
    ( spl7_108
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f1088,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_108 ),
    inference(superposition,[],[f108,f857])).

fof(f857,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_108 ),
    inference(avatar_component_clause,[],[f856])).

fof(f1022,plain,
    ( spl7_126
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f963,f364,f1020])).

fof(f1020,plain,
    ( spl7_126
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f364,plain,
    ( spl7_56
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f963,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_56 ),
    inference(unit_resulting_resolution,[],[f365,f97])).

fof(f365,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f364])).

fof(f1005,plain,
    ( spl7_70
    | ~ spl7_84
    | ~ spl7_108 ),
    inference(avatar_split_clause,[],[f956,f856,f599,f485])).

fof(f485,plain,
    ( spl7_70
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f599,plain,
    ( spl7_84
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f956,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_84
    | ~ spl7_108 ),
    inference(forward_demodulation,[],[f600,f857])).

fof(f600,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f599])).

fof(f958,plain,
    ( ~ spl7_66
    | ~ spl7_98 ),
    inference(avatar_contradiction_clause,[],[f957])).

fof(f957,plain,
    ( $false
    | ~ spl7_66
    | ~ spl7_98 ),
    inference(subsumption_resolution,[],[f436,f845])).

fof(f845,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_98 ),
    inference(unit_resulting_resolution,[],[f686,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t7_boole)).

fof(f436,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl7_66
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f952,plain,
    ( spl7_124
    | spl7_67 ),
    inference(avatar_split_clause,[],[f760,f438,f950])).

fof(f438,plain,
    ( spl7_67
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f760,plain,
    ( r2_hidden(sK4(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f108,f439,f111])).

fof(f439,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f438])).

fof(f945,plain,
    ( ~ spl7_123
    | spl7_67 ),
    inference(avatar_split_clause,[],[f759,f438,f943])).

fof(f943,plain,
    ( spl7_123
  <=> ~ r2_hidden(u1_struct_0(sK1),sK4(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_123])])).

fof(f759,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(u1_struct_0(sK1)))
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f108,f439,f263])).

fof(f938,plain,
    ( ~ spl7_121
    | spl7_81 ),
    inference(avatar_split_clause,[],[f576,f573,f936])).

fof(f936,plain,
    ( spl7_121
  <=> ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).

fof(f573,plain,
    ( spl7_81
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f576,plain,
    ( ~ r2_hidden(sK3,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_81 ),
    inference(unit_resulting_resolution,[],[f108,f574,f121])).

fof(f574,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f573])).

fof(f930,plain,
    ( ~ spl7_119
    | spl7_55 ),
    inference(avatar_split_clause,[],[f403,f358,f928])).

fof(f928,plain,
    ( spl7_119
  <=> ~ r2_hidden(u1_struct_0(sK1),sK4(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f358,plain,
    ( spl7_55
  <=> ~ m1_subset_1(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f403,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(k1_zfmisc_1(sK3)))
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f108,f359,f121])).

fof(f359,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),sK3)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f358])).

fof(f920,plain,
    ( ~ spl7_117
    | spl7_93 ),
    inference(avatar_split_clause,[],[f831,f663,f918])).

fof(f918,plain,
    ( spl7_117
  <=> ~ r2_hidden(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f663,plain,
    ( spl7_93
  <=> ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f831,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_93 ),
    inference(unit_resulting_resolution,[],[f664,f110])).

fof(f664,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_93 ),
    inference(avatar_component_clause,[],[f663])).

fof(f912,plain,
    ( spl7_114
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f904,f248,f241,f203,f175,f168,f147,f910])).

fof(f910,plain,
    ( spl7_114
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f904,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(backward_demodulation,[],[f902,f317])).

fof(f317,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f249,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',redefinition_k2_relset_1)).

fof(f896,plain,
    ( spl7_112
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f888,f248,f241,f203,f175,f168,f147,f894])).

fof(f894,plain,
    ( spl7_112
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f888,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(backward_demodulation,[],[f886,f342])).

fof(f342,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f249,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',redefinition_k1_relset_1)).

fof(f871,plain,
    ( spl7_110
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f859,f248,f241,f203,f175,f168,f147,f869])).

fof(f869,plain,
    ( spl7_110
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f859,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f148,f169,f176,f204,f242,f249,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f858,plain,
    ( spl7_108
    | ~ spl7_84 ),
    inference(avatar_split_clause,[],[f792,f599,f856])).

fof(f792,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_84 ),
    inference(unit_resulting_resolution,[],[f600,f97])).

fof(f840,plain,
    ( spl7_106
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f833,f248,f241,f203,f175,f168,f147,f838])).

fof(f833,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f148,f169,f176,f204,f242,f249,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f827,plain,
    ( ~ spl7_105
    | spl7_91 ),
    inference(avatar_split_clause,[],[f657,f650,f825])).

fof(f825,plain,
    ( spl7_105
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK4(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f657,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK4(k1_xboole_0)))
    | ~ spl7_91 ),
    inference(unit_resulting_resolution,[],[f651,f110])).

fof(f820,plain,
    ( ~ spl7_103
    | spl7_89 ),
    inference(avatar_split_clause,[],[f654,f643,f818])).

fof(f818,plain,
    ( spl7_103
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK4(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f654,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK4(sK3)))
    | ~ spl7_89 ),
    inference(unit_resulting_resolution,[],[f644,f110])).

fof(f745,plain,
    ( spl7_100
    | ~ spl7_18
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f699,f364,f196,f743])).

fof(f743,plain,
    ( spl7_100
  <=> v2_connsp_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f699,plain,
    ( v2_connsp_1(k1_xboole_0,sK1)
    | ~ spl7_18
    | ~ spl7_56 ),
    inference(backward_demodulation,[],[f694,f197])).

fof(f694,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_56 ),
    inference(unit_resulting_resolution,[],[f365,f97])).

fof(f689,plain,
    ( ~ spl7_70
    | ~ spl7_78 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl7_70
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f486,f618])).

fof(f618,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_78 ),
    inference(unit_resulting_resolution,[],[f550,f113])).

fof(f486,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f485])).

fof(f687,plain,
    ( spl7_98
    | spl7_67
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f637,f449,f438,f685])).

fof(f449,plain,
    ( spl7_68
  <=> m1_subset_1(sK4(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f637,plain,
    ( r2_hidden(sK4(sK3),u1_struct_0(sK1))
    | ~ spl7_67
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f439,f450,f111])).

fof(f450,plain,
    ( m1_subset_1(sK4(sK3),u1_struct_0(sK1))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f449])).

fof(f680,plain,
    ( ~ spl7_97
    | spl7_67
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f636,f449,f438,f678])).

fof(f636,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4(sK3))
    | ~ spl7_67
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f439,f450,f263])).

fof(f673,plain,
    ( ~ spl7_95
    | spl7_85 ),
    inference(avatar_split_clause,[],[f627,f596,f671])).

fof(f627,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_85 ),
    inference(unit_resulting_resolution,[],[f307,f597,f111])).

fof(f307,plain,(
    ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f108,f300])).

fof(f665,plain,
    ( ~ spl7_93
    | spl7_67 ),
    inference(avatar_split_clause,[],[f441,f438,f663])).

fof(f441,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_67 ),
    inference(unit_resulting_resolution,[],[f439,f298])).

fof(f652,plain,
    ( ~ spl7_91
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f619,f549,f650])).

fof(f619,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK4(k1_xboole_0)))
    | ~ spl7_78 ),
    inference(unit_resulting_resolution,[],[f550,f300])).

fof(f645,plain,
    ( ~ spl7_89
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f533,f417,f643])).

fof(f533,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK4(sK3)))
    | ~ spl7_64 ),
    inference(unit_resulting_resolution,[],[f418,f300])).

fof(f635,plain,
    ( ~ spl7_87
    | ~ spl7_32
    | spl7_41 ),
    inference(avatar_split_clause,[],[f613,f282,f248,f633])).

fof(f282,plain,
    ( spl7_41
  <=> ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f613,plain,
    ( ~ v2_connsp_1(k10_relat_1(sK2,sK3),sK0)
    | ~ spl7_32
    | ~ spl7_41 ),
    inference(backward_demodulation,[],[f607,f283])).

fof(f283,plain,
    ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f282])).

fof(f601,plain,
    ( spl7_84
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f593,f485,f599])).

fof(f593,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f108,f553,f111])).

fof(f553,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f108,f486,f122])).

fof(f591,plain,
    ( ~ spl7_83
    | spl7_81 ),
    inference(avatar_split_clause,[],[f577,f573,f589])).

fof(f589,plain,
    ( spl7_83
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f577,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_81 ),
    inference(unit_resulting_resolution,[],[f574,f110])).

fof(f575,plain,
    ( ~ spl7_81
    | ~ spl7_64
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f552,f485,f417,f573])).

fof(f552,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_64
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f418,f486,f122])).

fof(f551,plain,
    ( spl7_78
    | spl7_71 ),
    inference(avatar_split_clause,[],[f494,f482,f549])).

fof(f494,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | ~ spl7_71 ),
    inference(unit_resulting_resolution,[],[f108,f483,f111])).

fof(f544,plain,
    ( ~ spl7_77
    | spl7_71 ),
    inference(avatar_split_clause,[],[f493,f482,f542])).

fof(f493,plain,
    ( ~ r2_hidden(k1_xboole_0,sK4(k1_xboole_0))
    | ~ spl7_71 ),
    inference(unit_resulting_resolution,[],[f108,f483,f263])).

fof(f518,plain,
    ( ~ spl7_75
    | spl7_73 ),
    inference(avatar_split_clause,[],[f507,f503,f516])).

fof(f503,plain,
    ( spl7_73
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f507,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_73 ),
    inference(unit_resulting_resolution,[],[f504,f110])).

fof(f504,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f503])).

fof(f505,plain,
    ( ~ spl7_73
    | spl7_71 ),
    inference(avatar_split_clause,[],[f492,f482,f503])).

fof(f492,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_71 ),
    inference(unit_resulting_resolution,[],[f483,f298])).

fof(f487,plain,
    ( spl7_70
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f466,f364,f485])).

fof(f466,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_56 ),
    inference(backward_demodulation,[],[f456,f365])).

fof(f456,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_56 ),
    inference(unit_resulting_resolution,[],[f365,f97])).

fof(f451,plain,
    ( spl7_68
    | ~ spl7_28
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f425,f417,f234,f449])).

fof(f425,plain,
    ( m1_subset_1(sK4(sK3),u1_struct_0(sK1))
    | ~ spl7_28
    | ~ spl7_64 ),
    inference(unit_resulting_resolution,[],[f235,f418,f121])).

fof(f440,plain,
    ( ~ spl7_67
    | ~ spl7_28
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f426,f417,f234,f438])).

fof(f426,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_28
    | ~ spl7_64 ),
    inference(unit_resulting_resolution,[],[f235,f418,f122])).

fof(f419,plain,
    ( spl7_64
    | spl7_57 ),
    inference(avatar_split_clause,[],[f375,f361,f417])).

fof(f361,plain,
    ( spl7_57
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f375,plain,
    ( r2_hidden(sK4(sK3),sK3)
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f108,f362,f111])).

fof(f362,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f361])).

fof(f412,plain,
    ( ~ spl7_63
    | spl7_57 ),
    inference(avatar_split_clause,[],[f374,f361,f410])).

fof(f374,plain,
    ( ~ r2_hidden(sK3,sK4(sK3))
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f108,f362,f263])).

fof(f394,plain,
    ( ~ spl7_61
    | spl7_59 ),
    inference(avatar_split_clause,[],[f386,f382,f392])).

fof(f392,plain,
    ( spl7_61
  <=> ~ r2_hidden(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f382,plain,
    ( spl7_59
  <=> ~ m1_subset_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f386,plain,
    ( ~ r2_hidden(sK3,sK3)
    | ~ spl7_59 ),
    inference(unit_resulting_resolution,[],[f383,f110])).

fof(f383,plain,
    ( ~ m1_subset_1(sK3,sK3)
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f382])).

fof(f384,plain,
    ( ~ spl7_59
    | spl7_57 ),
    inference(avatar_split_clause,[],[f373,f361,f382])).

fof(f373,plain,
    ( ~ m1_subset_1(sK3,sK3)
    | ~ spl7_57 ),
    inference(unit_resulting_resolution,[],[f362,f298])).

fof(f366,plain,
    ( ~ spl7_55
    | spl7_56
    | spl7_45 ),
    inference(avatar_split_clause,[],[f316,f313,f364,f358])).

fof(f313,plain,
    ( spl7_45
  <=> ~ r2_hidden(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f316,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),sK3)
    | ~ spl7_45 ),
    inference(resolution,[],[f314,f111])).

fof(f314,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f313])).

fof(f350,plain,
    ( ~ spl7_53
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f304,f289,f348])).

fof(f348,plain,
    ( spl7_53
  <=> ~ r2_hidden(u1_struct_0(sK6),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f289,plain,
    ( spl7_42
  <=> m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f304,plain,
    ( ~ r2_hidden(u1_struct_0(sK6),k2_struct_0(sK6))
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f290,f300])).

fof(f290,plain,
    ( m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f289])).

fof(f341,plain,
    ( ~ spl7_51
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f303,f259,f339])).

fof(f339,plain,
    ( spl7_51
  <=> ~ r2_hidden(u1_struct_0(sK5),k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f259,plain,
    ( spl7_34
  <=> m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f303,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),k2_struct_0(sK5))
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f260,f300])).

fof(f260,plain,
    ( m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f259])).

fof(f332,plain,
    ( ~ spl7_49
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f302,f275,f330])).

fof(f330,plain,
    ( spl7_49
  <=> ~ r2_hidden(u1_struct_0(sK1),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f275,plain,
    ( spl7_38
  <=> m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f302,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),k2_struct_0(sK1))
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f276,f300])).

fof(f276,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f275])).

fof(f325,plain,
    ( ~ spl7_47
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f301,f268,f323])).

fof(f323,plain,
    ( spl7_47
  <=> ~ r2_hidden(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f268,plain,
    ( spl7_36
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f301,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f269,f300])).

fof(f269,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f268])).

fof(f315,plain,
    ( ~ spl7_45
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f306,f234,f313])).

fof(f306,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3)
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f235,f300])).

fof(f291,plain,
    ( spl7_42
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f254,f227,f289])).

fof(f227,plain,
    ( spl7_26
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f254,plain,
    ( m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f228,f98])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',dt_k2_struct_0)).

fof(f228,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f284,plain,(
    ~ spl7_41 ),
    inference(avatar_split_clause,[],[f96,f282])).

fof(f96,plain,(
    ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK0)
    & v2_connsp_1(sK3,sK1)
    & v3_tops_2(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f74,f73,f72,f71])).

fof(f71,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v2_connsp_1(X3,X1)
                    & v3_tops_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),sK0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,sK0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),X0)
                & v2_connsp_1(X3,sK1)
                & v3_tops_2(X2,X0,sK1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
              & v2_connsp_1(X3,X1)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),X0)
            & v2_connsp_1(X3,X1)
            & v3_tops_2(sK2,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v2_connsp_1(X3,X1)
          & v3_tops_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),X0)
        & v2_connsp_1(sK3,X1)
        & v3_tops_2(X2,X0,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                  & v2_connsp_1(X3,X1)
                  & v3_tops_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_connsp_1(X3,X1)
                        & v3_tops_2(X2,X0,X1) )
                     => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_connsp_1(X3,X1)
                      & v3_tops_2(X2,X0,X1) )
                   => v2_connsp_1(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',t76_tops_2)).

fof(f277,plain,
    ( spl7_38
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f252,f220,f275])).

fof(f252,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f221,f98])).

fof(f270,plain,
    ( spl7_36
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f251,f213,f268])).

fof(f251,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f214,f98])).

fof(f261,plain,
    ( spl7_34
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f253,f182,f259])).

fof(f182,plain,
    ( spl7_14
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f253,plain,
    ( m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f183,f98])).

fof(f183,plain,
    ( l1_struct_0(sK5)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f250,plain,(
    spl7_32 ),
    inference(avatar_split_clause,[],[f92,f248])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f75])).

fof(f243,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f91,f241])).

fof(f91,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f75])).

fof(f236,plain,(
    spl7_28 ),
    inference(avatar_split_clause,[],[f93,f234])).

fof(f93,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f75])).

fof(f229,plain,
    ( spl7_26
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f208,f189,f227])).

fof(f189,plain,
    ( spl7_16
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f208,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f190,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',dt_l1_pre_topc)).

fof(f190,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f222,plain,
    ( spl7_24
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f207,f168,f220])).

fof(f207,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f169,f100])).

fof(f215,plain,
    ( spl7_22
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f206,f147,f213])).

fof(f206,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f148,f100])).

fof(f205,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f94,f203])).

fof(f94,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f198,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f95,f196])).

fof(f95,plain,(
    v2_connsp_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f191,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f128,f189])).

fof(f128,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f82])).

fof(f82,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',existence_l1_pre_topc)).

fof(f184,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f127,f182])).

fof(f127,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f80])).

fof(f80,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t76_tops_2.p',existence_l1_struct_0)).

fof(f177,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f90,f175])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f170,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f89,f168])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f163,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f88,f161])).

fof(f88,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f156,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f87,f154])).

fof(f87,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

fof(f149,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f86,f147])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f142,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f85,f140])).

fof(f85,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f135,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f84,f133])).

fof(f84,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).
%------------------------------------------------------------------------------
