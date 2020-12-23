%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t11_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:06 EDT 2019

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  626 (2125 expanded)
%              Number of leaves         :  157 ( 910 expanded)
%              Depth                    :   15
%              Number of atoms          : 2479 (6948 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1779,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f133,f140,f147,f154,f161,f168,f175,f182,f192,f202,f216,f223,f232,f240,f249,f256,f271,f285,f301,f311,f322,f330,f337,f344,f353,f360,f367,f384,f395,f409,f416,f457,f464,f476,f483,f490,f505,f520,f527,f550,f559,f572,f580,f603,f614,f621,f628,f635,f653,f667,f674,f688,f698,f705,f712,f719,f736,f746,f753,f786,f801,f808,f823,f834,f841,f848,f855,f862,f877,f884,f891,f900,f917,f924,f939,f1007,f1019,f1088,f1126,f1143,f1150,f1162,f1177,f1187,f1194,f1201,f1208,f1215,f1224,f1231,f1238,f1295,f1342,f1351,f1398,f1407,f1425,f1434,f1452,f1462,f1469,f1479,f1488,f1514,f1521,f1528,f1537,f1545,f1552,f1559,f1584,f1594,f1601,f1608,f1617,f1635,f1642,f1649,f1656,f1666,f1675,f1691,f1698,f1716,f1750,f1757,f1768,f1777])).

fof(f1777,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | spl8_197 ),
    inference(avatar_contradiction_clause,[],[f1776])).

fof(f1776,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1775,f125])).

fof(f125,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_1
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1775,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1774,f160])).

fof(f160,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl8_10
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f1774,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1773,f132])).

fof(f132,plain,
    ( v3_relat_2(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_2
  <=> v3_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1773,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1772,f139])).

fof(f139,plain,
    ( v8_relat_2(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl8_4
  <=> v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1772,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1771,f201])).

fof(f201,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl8_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1771,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1770,f359])).

fof(f359,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl8_52
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f1770,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1769,f634])).

fof(f634,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl8_96 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl8_96
  <=> v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f1769,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1765,f512])).

fof(f512,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f125,f300,f174,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
          | ~ m2_filter_1(X2,X0,X1) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_filter_1(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',dt_m2_filter_1)).

fof(f174,plain,
    ( m2_filter_1(sK3,sK0,sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl8_14
  <=> m2_filter_1(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f300,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl8_38
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1765,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_197 ),
    inference(resolution,[],[f1282,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(X1)
        & v3_relat_2(X1)
        & v1_partfun1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k3_filter_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))))
        & v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
        & v1_funct_1(k3_filter_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',dt_k3_filter_1)).

fof(f1282,plain,
    ( ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ spl8_197 ),
    inference(avatar_component_clause,[],[f1281])).

fof(f1281,plain,
    ( spl8_197
  <=> ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_197])])).

fof(f1768,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | spl8_197 ),
    inference(avatar_contradiction_clause,[],[f1767])).

fof(f1767,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(subsumption_resolution,[],[f1758,f512])).

fof(f1758,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_197 ),
    inference(unit_resulting_resolution,[],[f125,f359,f132,f139,f160,f201,f634,f1282,f116])).

fof(f1757,plain,
    ( ~ spl8_245
    | ~ spl8_6
    | ~ spl8_150 ),
    inference(avatar_split_clause,[],[f1132,f931,f145,f1755])).

fof(f1755,plain,
    ( spl8_245
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_245])])).

fof(f145,plain,
    ( spl8_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f931,plain,
    ( spl8_150
  <=> r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f1132,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_150 ),
    inference(unit_resulting_resolution,[],[f932,f315])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f118,f146])).

fof(f146,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t5_subset)).

fof(f932,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_150 ),
    inference(avatar_component_clause,[],[f931])).

fof(f1750,plain,
    ( spl8_242
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f551,f548,f1748])).

fof(f1748,plain,
    ( spl8_242
  <=> m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_242])])).

fof(f548,plain,
    ( spl8_80
  <=> m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f551,plain,
    ( m1_subset_1(k8_eqrel_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl8_80 ),
    inference(unit_resulting_resolution,[],[f549,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_eqrel_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_eqrel_1(X1,X0)
     => m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',dt_m1_eqrel_1)).

fof(f549,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f548])).

fof(f1716,plain,
    ( spl8_240
    | ~ spl8_190 ),
    inference(avatar_split_clause,[],[f1708,f1260,f1714])).

fof(f1714,plain,
    ( spl8_240
  <=> v1_relat_1(k3_filter_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_240])])).

fof(f1260,plain,
    ( spl8_190
  <=> m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_190])])).

fof(f1708,plain,
    ( v1_relat_1(k3_filter_1(sK0,sK1,sK2))
    | ~ spl8_190 ),
    inference(unit_resulting_resolution,[],[f1261,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',cc1_relset_1)).

fof(f1261,plain,
    ( m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ spl8_190 ),
    inference(avatar_component_clause,[],[f1260])).

fof(f1698,plain,
    ( ~ spl8_239
    | ~ spl8_6
    | spl8_133 ),
    inference(avatar_split_clause,[],[f868,f846,f145,f1696])).

fof(f1696,plain,
    ( spl8_239
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_239])])).

fof(f846,plain,
    ( spl8_133
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).

fof(f868,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK7))))
    | ~ spl8_6
    | ~ spl8_133 ),
    inference(unit_resulting_resolution,[],[f847,f207])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_eqrel_1(o_0_0_xboole_0,X0)
        | v1_xboole_0(X0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f91,f146])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_eqrel_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | ~ m1_eqrel_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_eqrel_1(X1,X0)
         => ~ v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',cc1_eqrel_1)).

fof(f847,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK7))))
    | ~ spl8_133 ),
    inference(avatar_component_clause,[],[f846])).

fof(f1691,plain,
    ( ~ spl8_237
    | spl8_133 ),
    inference(avatar_split_clause,[],[f864,f846,f1689])).

fof(f1689,plain,
    ( spl8_237
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_237])])).

fof(f864,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK7)))))
    | ~ spl8_133 ),
    inference(unit_resulting_resolution,[],[f95,f847,f91])).

fof(f95,plain,(
    ! [X0] : m1_eqrel_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] : m1_eqrel_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] : m1_eqrel_1(X1,X0)
     => m1_eqrel_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_eqrel_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',existence_m1_eqrel_1)).

fof(f1675,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | spl8_191 ),
    inference(avatar_contradiction_clause,[],[f1674])).

fof(f1674,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1673,f125])).

fof(f1673,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1672,f160])).

fof(f1672,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1671,f132])).

fof(f1671,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1670,f139])).

fof(f1670,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1669,f201])).

fof(f1669,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1668,f352])).

fof(f352,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl8_50
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f1668,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1667,f627])).

fof(f627,plain,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl8_94
  <=> v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f1667,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1663,f511])).

fof(f511,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f125,f300,f167,f103])).

fof(f167,plain,
    ( m2_filter_1(sK2,sK0,sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_12
  <=> m2_filter_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f1663,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_191 ),
    inference(resolution,[],[f1264,f116])).

fof(f1264,plain,
    ( ~ m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ spl8_191 ),
    inference(avatar_component_clause,[],[f1263])).

fof(f1263,plain,
    ( spl8_191
  <=> ~ m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_191])])).

fof(f1666,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | spl8_191 ),
    inference(avatar_contradiction_clause,[],[f1665])).

fof(f1665,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(subsumption_resolution,[],[f1657,f511])).

fof(f1657,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_191 ),
    inference(unit_resulting_resolution,[],[f125,f352,f132,f139,f160,f201,f627,f1264,f116])).

fof(f1656,plain,
    ( ~ spl8_235
    | ~ spl8_6
    | spl8_111 ),
    inference(avatar_split_clause,[],[f725,f710,f145,f1654])).

fof(f1654,plain,
    ( spl8_235
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_235])])).

fof(f710,plain,
    ( spl8_111
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f725,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(k1_zfmisc_1(sK0))))
    | ~ spl8_6
    | ~ spl8_111 ),
    inference(unit_resulting_resolution,[],[f711,f207])).

fof(f711,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK0))))
    | ~ spl8_111 ),
    inference(avatar_component_clause,[],[f710])).

fof(f1649,plain,
    ( ~ spl8_233
    | spl8_111 ),
    inference(avatar_split_clause,[],[f721,f710,f1647])).

fof(f1647,plain,
    ( spl8_233
  <=> ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_233])])).

fof(f721,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(k1_zfmisc_1(sK0)))))
    | ~ spl8_111 ),
    inference(unit_resulting_resolution,[],[f95,f711,f91])).

fof(f1642,plain,
    ( ~ spl8_231
    | ~ spl8_220 ),
    inference(avatar_split_clause,[],[f1620,f1557,f1640])).

fof(f1640,plain,
    ( spl8_231
  <=> ~ r2_hidden(k1_zfmisc_1(sK7),sK5(sK4(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_231])])).

fof(f1557,plain,
    ( spl8_220
  <=> r2_hidden(sK5(sK4(sK7)),k1_zfmisc_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_220])])).

fof(f1620,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK7),sK5(sK4(sK7)))
    | ~ spl8_220 ),
    inference(unit_resulting_resolution,[],[f1558,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',antisymmetry_r2_hidden)).

fof(f1558,plain,
    ( r2_hidden(sK5(sK4(sK7)),k1_zfmisc_1(sK7))
    | ~ spl8_220 ),
    inference(avatar_component_clause,[],[f1557])).

fof(f1635,plain,
    ( ~ spl8_229
    | ~ spl8_180 ),
    inference(avatar_split_clause,[],[f1491,f1222,f1633])).

fof(f1633,plain,
    ( spl8_229
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK5(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_229])])).

fof(f1222,plain,
    ( spl8_180
  <=> r2_hidden(sK5(sK4(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_180])])).

fof(f1491,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK5(sK4(sK0)))
    | ~ spl8_180 ),
    inference(unit_resulting_resolution,[],[f1223,f97])).

fof(f1223,plain,
    ( r2_hidden(sK5(sK4(sK0)),k1_zfmisc_1(sK0))
    | ~ spl8_180 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1617,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | spl8_195 ),
    inference(avatar_contradiction_clause,[],[f1616])).

fof(f1616,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1615,f125])).

fof(f1615,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1614,f160])).

fof(f1614,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1613,f132])).

fof(f1613,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1612,f139])).

fof(f1612,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1611,f201])).

fof(f1611,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1610,f359])).

fof(f1610,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1609,f634])).

fof(f1609,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1605,f512])).

fof(f1605,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_195 ),
    inference(resolution,[],[f1276,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_filter_1(X0,X1,X2),k2_zfmisc_1(k8_eqrel_1(X0,X1),k8_eqrel_1(X0,X1)),k8_eqrel_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1276,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ spl8_195 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f1275,plain,
    ( spl8_195
  <=> ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_195])])).

fof(f1608,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | spl8_195 ),
    inference(avatar_contradiction_clause,[],[f1607])).

fof(f1607,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(subsumption_resolution,[],[f1602,f512])).

fof(f1602,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_195 ),
    inference(unit_resulting_resolution,[],[f125,f359,f132,f139,f160,f201,f634,f1276,f115])).

fof(f1601,plain,
    ( ~ spl8_227
    | spl8_223 ),
    inference(avatar_split_clause,[],[f1587,f1582,f1599])).

fof(f1599,plain,
    ( spl8_227
  <=> ~ r2_hidden(k1_zfmisc_1(sK7),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_227])])).

fof(f1582,plain,
    ( spl8_223
  <=> ~ m1_subset_1(k1_zfmisc_1(sK7),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_223])])).

fof(f1587,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK7),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_223 ),
    inference(unit_resulting_resolution,[],[f1583,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t1_subset)).

fof(f1583,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK7),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_223 ),
    inference(avatar_component_clause,[],[f1582])).

fof(f1594,plain,
    ( ~ spl8_225
    | spl8_223 ),
    inference(avatar_split_clause,[],[f1585,f1582,f1592])).

fof(f1592,plain,
    ( spl8_225
  <=> ~ r2_hidden(k1_zfmisc_1(sK7),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_225])])).

fof(f1585,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK7),sK4(o_0_0_xboole_0))
    | ~ spl8_223 ),
    inference(unit_resulting_resolution,[],[f233,f1583,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t4_subset)).

fof(f233,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f95,f99])).

fof(f1584,plain,
    ( ~ spl8_223
    | ~ spl8_6
    | ~ spl8_216 ),
    inference(avatar_split_clause,[],[f1573,f1543,f145,f1582])).

fof(f1543,plain,
    ( spl8_216
  <=> r2_hidden(sK5(k1_zfmisc_1(sK7)),k1_zfmisc_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_216])])).

fof(f1573,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK7),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_216 ),
    inference(unit_resulting_resolution,[],[f1544,f315])).

fof(f1544,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK7)),k1_zfmisc_1(sK7))
    | ~ spl8_216 ),
    inference(avatar_component_clause,[],[f1543])).

fof(f1559,plain,
    ( spl8_220
    | spl8_121
    | ~ spl8_148 ),
    inference(avatar_split_clause,[],[f925,f922,f784,f1557])).

fof(f784,plain,
    ( spl8_121
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_121])])).

fof(f922,plain,
    ( spl8_148
  <=> m1_subset_1(sK5(sK4(sK7)),k1_zfmisc_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).

fof(f925,plain,
    ( r2_hidden(sK5(sK4(sK7)),k1_zfmisc_1(sK7))
    | ~ spl8_121
    | ~ spl8_148 ),
    inference(unit_resulting_resolution,[],[f785,f923,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t2_subset)).

fof(f923,plain,
    ( m1_subset_1(sK5(sK4(sK7)),k1_zfmisc_1(sK7))
    | ~ spl8_148 ),
    inference(avatar_component_clause,[],[f922])).

fof(f785,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK7))
    | ~ spl8_121 ),
    inference(avatar_component_clause,[],[f784])).

fof(f1552,plain,
    ( ~ spl8_219
    | spl8_121 ),
    inference(avatar_split_clause,[],[f794,f784,f1550])).

fof(f1550,plain,
    ( spl8_219
  <=> ~ r2_hidden(k1_zfmisc_1(sK7),sK5(k1_zfmisc_1(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_219])])).

fof(f794,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK7),sK5(k1_zfmisc_1(sK7)))
    | ~ spl8_121 ),
    inference(unit_resulting_resolution,[],[f785,f539])).

fof(f539,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK5(X3))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f262,f97])).

fof(f262,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f100,f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',existence_m1_subset_1)).

fof(f1545,plain,
    ( spl8_216
    | spl8_121 ),
    inference(avatar_split_clause,[],[f793,f784,f1543])).

fof(f793,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK7)),k1_zfmisc_1(sK7))
    | ~ spl8_121 ),
    inference(unit_resulting_resolution,[],[f785,f262])).

fof(f1537,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | spl8_189 ),
    inference(avatar_contradiction_clause,[],[f1536])).

fof(f1536,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1535,f125])).

fof(f1535,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1534,f160])).

fof(f1534,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1533,f132])).

fof(f1533,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1532,f139])).

fof(f1532,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1531,f201])).

fof(f1531,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1530,f352])).

fof(f1530,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1529,f627])).

fof(f1529,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1525,f511])).

fof(f1525,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_189 ),
    inference(resolution,[],[f1258,f115])).

fof(f1258,plain,
    ( ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ spl8_189 ),
    inference(avatar_component_clause,[],[f1257])).

fof(f1257,plain,
    ( spl8_189
  <=> ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_189])])).

fof(f1528,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | spl8_189 ),
    inference(avatar_contradiction_clause,[],[f1527])).

fof(f1527,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(subsumption_resolution,[],[f1522,f511])).

fof(f1522,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_189 ),
    inference(unit_resulting_resolution,[],[f125,f352,f132,f139,f160,f201,f627,f1258,f115])).

fof(f1521,plain,
    ( ~ spl8_215
    | spl8_71 ),
    inference(avatar_split_clause,[],[f497,f481,f1519])).

fof(f1519,plain,
    ( spl8_215
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_215])])).

fof(f481,plain,
    ( spl8_71
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f497,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK7)))))
    | ~ spl8_71 ),
    inference(unit_resulting_resolution,[],[f95,f482,f91])).

fof(f482,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK7))))
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f481])).

fof(f1514,plain,
    ( ~ spl8_213
    | ~ spl8_6
    | spl8_71 ),
    inference(avatar_split_clause,[],[f496,f481,f145,f1512])).

fof(f1512,plain,
    ( spl8_213
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_213])])).

fof(f496,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK7))))
    | ~ spl8_6
    | ~ spl8_71 ),
    inference(unit_resulting_resolution,[],[f146,f482,f91])).

fof(f1488,plain,
    ( spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_52
    | ~ spl8_94
    | ~ spl8_96
    | spl8_211 ),
    inference(avatar_contradiction_clause,[],[f1487])).

fof(f1487,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_52
    | ~ spl8_94
    | ~ spl8_96
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1486,f352])).

fof(f1486,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_94
    | ~ spl8_96
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1485,f627])).

fof(f1485,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1484,f511])).

fof(f1484,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1483,f359])).

fof(f1483,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_96
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1482,f634])).

fof(f1482,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1481,f512])).

fof(f1481,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_16
    | ~ spl8_211 ),
    inference(subsumption_resolution,[],[f1480,f181])).

fof(f181,plain,
    ( r6_binop_1(sK0,sK2,sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl8_16
  <=> r6_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f1480,plain,
    ( ~ r6_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_211 ),
    inference(resolution,[],[f1478,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r5_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r6_binop_1(X0,X1,X2)
              | ~ r5_binop_1(X0,X1,X2)
              | ~ r4_binop_1(X0,X1,X2) )
            & ( ( r5_binop_1(X0,X1,X2)
                & r4_binop_1(X0,X1,X2) )
              | ~ r6_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
          | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
          | ~ v1_funct_1(X2) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
            & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
            & v1_funct_1(X2) )
         => ( r6_binop_1(X0,X1,X2)
          <=> ( r5_binop_1(X0,X1,X2)
              & r4_binop_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',d11_binop_1)).

fof(f1478,plain,
    ( ~ r5_binop_1(sK0,sK2,sK3)
    | ~ spl8_211 ),
    inference(avatar_component_clause,[],[f1477])).

fof(f1477,plain,
    ( spl8_211
  <=> ~ r5_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_211])])).

fof(f1479,plain,
    ( ~ spl8_211
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | spl8_201 ),
    inference(avatar_split_clause,[],[f1470,f1293,f200,f173,f166,f159,f138,f131,f124,f1477])).

fof(f1293,plain,
    ( spl8_201
  <=> ~ r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_201])])).

fof(f1470,plain,
    ( ~ r5_binop_1(sK0,sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_201 ),
    inference(unit_resulting_resolution,[],[f125,f139,f132,f160,f167,f174,f201,f1294,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r5_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r5_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r5_binop_1(X0,X2,X3)
                   => r5_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t10_filter_1)).

fof(f1294,plain,
    ( ~ r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl8_201 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1469,plain,
    ( ~ spl8_209
    | spl8_205 ),
    inference(avatar_split_clause,[],[f1455,f1450,f1467])).

fof(f1467,plain,
    ( spl8_209
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_209])])).

fof(f1450,plain,
    ( spl8_205
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_205])])).

fof(f1455,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_205 ),
    inference(unit_resulting_resolution,[],[f1451,f98])).

fof(f1451,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_205 ),
    inference(avatar_component_clause,[],[f1450])).

fof(f1462,plain,
    ( ~ spl8_207
    | spl8_205 ),
    inference(avatar_split_clause,[],[f1453,f1450,f1460])).

fof(f1460,plain,
    ( spl8_207
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_207])])).

fof(f1453,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK4(o_0_0_xboole_0))
    | ~ spl8_205 ),
    inference(unit_resulting_resolution,[],[f233,f1451,f117])).

fof(f1452,plain,
    ( ~ spl8_205
    | ~ spl8_6
    | ~ spl8_176 ),
    inference(avatar_split_clause,[],[f1441,f1206,f145,f1450])).

fof(f1206,plain,
    ( spl8_176
  <=> r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_176])])).

fof(f1441,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_176 ),
    inference(unit_resulting_resolution,[],[f1207,f315])).

fof(f1207,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl8_176 ),
    inference(avatar_component_clause,[],[f1206])).

fof(f1434,plain,
    ( spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_52
    | ~ spl8_94
    | ~ spl8_96
    | spl8_203 ),
    inference(avatar_contradiction_clause,[],[f1433])).

fof(f1433,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_52
    | ~ spl8_94
    | ~ spl8_96
    | ~ spl8_203 ),
    inference(subsumption_resolution,[],[f1432,f352])).

fof(f1432,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_94
    | ~ spl8_96
    | ~ spl8_203 ),
    inference(subsumption_resolution,[],[f1431,f627])).

fof(f1431,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_203 ),
    inference(subsumption_resolution,[],[f1430,f511])).

fof(f1430,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_203 ),
    inference(subsumption_resolution,[],[f1429,f359])).

fof(f1429,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_96
    | ~ spl8_203 ),
    inference(subsumption_resolution,[],[f1428,f634])).

fof(f1428,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_203 ),
    inference(subsumption_resolution,[],[f1427,f512])).

fof(f1427,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_16
    | ~ spl8_203 ),
    inference(subsumption_resolution,[],[f1426,f181])).

fof(f1426,plain,
    ( ~ r6_binop_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl8_203 ),
    inference(resolution,[],[f1424,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r4_binop_1(X0,X1,X2)
      | ~ r6_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1424,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ spl8_203 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f1423,plain,
    ( spl8_203
  <=> ~ r4_binop_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_203])])).

fof(f1425,plain,
    ( ~ spl8_203
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | spl8_199 ),
    inference(avatar_split_clause,[],[f1416,f1287,f200,f173,f166,f159,f138,f131,f124,f1423])).

fof(f1287,plain,
    ( spl8_199
  <=> ~ r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_199])])).

fof(f1416,plain,
    ( ~ r4_binop_1(sK0,sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_199 ),
    inference(unit_resulting_resolution,[],[f125,f139,f132,f160,f167,f174,f201,f1288,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
      | ~ r4_binop_1(X0,X2,X3)
      | ~ m2_filter_1(X3,X0,X1)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  | ~ r4_binop_1(X0,X2,X3)
                  | ~ m2_filter_1(X3,X0,X1) )
              | ~ m2_filter_1(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          | ~ v8_relat_2(X1)
          | ~ v3_relat_2(X1)
          | ~ v1_partfun1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r4_binop_1(X0,X2,X3)
                   => r4_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t9_filter_1)).

fof(f1288,plain,
    ( ~ r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl8_199 ),
    inference(avatar_component_clause,[],[f1287])).

fof(f1407,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | spl8_193 ),
    inference(avatar_contradiction_clause,[],[f1406])).

fof(f1406,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1405,f125])).

fof(f1405,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1404,f160])).

fof(f1404,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1403,f132])).

fof(f1403,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1402,f139])).

fof(f1402,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1401,f201])).

fof(f1401,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1400,f359])).

fof(f1400,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1399,f634])).

fof(f1399,plain,
    ( ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1395,f512])).

fof(f1395,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_193 ),
    inference(resolution,[],[f1270,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_filter_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1)
      | ~ v1_partfun1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1270,plain,
    ( ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ spl8_193 ),
    inference(avatar_component_clause,[],[f1269])).

fof(f1269,plain,
    ( spl8_193
  <=> ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_193])])).

fof(f1398,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | spl8_193 ),
    inference(avatar_contradiction_clause,[],[f1397])).

fof(f1397,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(subsumption_resolution,[],[f1352,f512])).

fof(f1352,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_52
    | ~ spl8_96
    | ~ spl8_193 ),
    inference(unit_resulting_resolution,[],[f125,f359,f132,f139,f160,f201,f634,f1270,f114])).

fof(f1351,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | spl8_187 ),
    inference(avatar_contradiction_clause,[],[f1350])).

fof(f1350,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1349,f125])).

fof(f1349,plain,
    ( v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1348,f160])).

fof(f1348,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1347,f132])).

fof(f1347,plain,
    ( ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1346,f139])).

fof(f1346,plain,
    ( ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1345,f201])).

fof(f1345,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1344,f352])).

fof(f1344,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1343,f627])).

fof(f1343,plain,
    ( ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1339,f511])).

fof(f1339,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v8_relat_2(sK1)
    | ~ v3_relat_2(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl8_187 ),
    inference(resolution,[],[f1252,f114])).

fof(f1252,plain,
    ( ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2))
    | ~ spl8_187 ),
    inference(avatar_component_clause,[],[f1251])).

fof(f1251,plain,
    ( spl8_187
  <=> ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_187])])).

fof(f1342,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | spl8_187 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_20
    | ~ spl8_38
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(subsumption_resolution,[],[f1296,f511])).

fof(f1296,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20
    | ~ spl8_50
    | ~ spl8_94
    | ~ spl8_187 ),
    inference(unit_resulting_resolution,[],[f125,f352,f132,f139,f160,f201,f627,f1252,f114])).

fof(f1295,plain,
    ( ~ spl8_187
    | ~ spl8_189
    | ~ spl8_191
    | ~ spl8_193
    | ~ spl8_195
    | ~ spl8_197
    | ~ spl8_199
    | ~ spl8_201
    | spl8_61 ),
    inference(avatar_split_clause,[],[f754,f407,f1293,f1287,f1281,f1275,f1269,f1263,f1257,f1251])).

fof(f407,plain,
    ( spl8_61
  <=> ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f754,plain,
    ( ~ r5_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ r4_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK3),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK3))
    | ~ m1_subset_1(k3_filter_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))))
    | ~ v1_funct_2(k3_filter_1(sK0,sK1,sK2),k2_zfmisc_1(k8_eqrel_1(sK0,sK1),k8_eqrel_1(sK0,sK1)),k8_eqrel_1(sK0,sK1))
    | ~ v1_funct_1(k3_filter_1(sK0,sK1,sK2))
    | ~ spl8_61 ),
    inference(resolution,[],[f110,f408])).

fof(f408,plain,
    ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f407])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r6_binop_1(X0,X1,X2)
      | ~ r5_binop_1(X0,X1,X2)
      | ~ r4_binop_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1238,plain,
    ( ~ spl8_185
    | ~ spl8_6
    | spl8_157 ),
    inference(avatar_split_clause,[],[f1110,f1014,f145,f1236])).

fof(f1236,plain,
    ( spl8_185
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_185])])).

fof(f1014,plain,
    ( spl8_157
  <=> ~ v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).

fof(f1110,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_6
    | ~ spl8_157 ),
    inference(unit_resulting_resolution,[],[f1015,f207])).

fof(f1015,plain,
    ( ~ v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_157 ),
    inference(avatar_component_clause,[],[f1014])).

fof(f1231,plain,
    ( ~ spl8_183
    | spl8_157 ),
    inference(avatar_split_clause,[],[f1106,f1014,f1229])).

fof(f1229,plain,
    ( spl8_183
  <=> ~ v1_xboole_0(sK4(sK4(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_183])])).

fof(f1106,plain,
    ( ~ v1_xboole_0(sK4(sK4(k2_zfmisc_1(sK0,sK0))))
    | ~ spl8_157 ),
    inference(unit_resulting_resolution,[],[f95,f1015,f91])).

fof(f1224,plain,
    ( spl8_180
    | spl8_99
    | ~ spl8_140 ),
    inference(avatar_split_clause,[],[f892,f882,f651,f1222])).

fof(f651,plain,
    ( spl8_99
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f882,plain,
    ( spl8_140
  <=> m1_subset_1(sK5(sK4(sK0)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).

fof(f892,plain,
    ( r2_hidden(sK5(sK4(sK0)),k1_zfmisc_1(sK0))
    | ~ spl8_99
    | ~ spl8_140 ),
    inference(unit_resulting_resolution,[],[f652,f883,f100])).

fof(f883,plain,
    ( m1_subset_1(sK5(sK4(sK0)),k1_zfmisc_1(sK0))
    | ~ spl8_140 ),
    inference(avatar_component_clause,[],[f882])).

fof(f652,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl8_99 ),
    inference(avatar_component_clause,[],[f651])).

fof(f1215,plain,
    ( ~ spl8_179
    | spl8_99 ),
    inference(avatar_split_clause,[],[f755,f651,f1213])).

fof(f1213,plain,
    ( spl8_179
  <=> ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_179])])).

fof(f755,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK0),sK5(k1_zfmisc_1(sK0)))
    | ~ spl8_99 ),
    inference(unit_resulting_resolution,[],[f652,f539])).

fof(f1208,plain,
    ( spl8_176
    | spl8_99 ),
    inference(avatar_split_clause,[],[f660,f651,f1206])).

fof(f660,plain,
    ( r2_hidden(sK5(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl8_99 ),
    inference(unit_resulting_resolution,[],[f652,f262])).

fof(f1201,plain,
    ( ~ spl8_175
    | ~ spl8_6
    | spl8_85 ),
    inference(avatar_split_clause,[],[f585,f570,f145,f1199])).

fof(f1199,plain,
    ( spl8_175
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k8_eqrel_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_175])])).

fof(f570,plain,
    ( spl8_85
  <=> ~ v1_xboole_0(sK4(k8_eqrel_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f585,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k8_eqrel_1(sK0,sK1)))
    | ~ spl8_6
    | ~ spl8_85 ),
    inference(unit_resulting_resolution,[],[f571,f207])).

fof(f571,plain,
    ( ~ v1_xboole_0(sK4(k8_eqrel_1(sK0,sK1)))
    | ~ spl8_85 ),
    inference(avatar_component_clause,[],[f570])).

fof(f1194,plain,
    ( ~ spl8_173
    | spl8_85 ),
    inference(avatar_split_clause,[],[f582,f570,f1192])).

fof(f1192,plain,
    ( spl8_173
  <=> ~ v1_xboole_0(sK4(sK4(k8_eqrel_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_173])])).

fof(f582,plain,
    ( ~ v1_xboole_0(sK4(sK4(k8_eqrel_1(sK0,sK1))))
    | ~ spl8_85 ),
    inference(unit_resulting_resolution,[],[f95,f571,f91])).

fof(f1187,plain,
    ( ~ spl8_171
    | spl8_67 ),
    inference(avatar_split_clause,[],[f469,f462,f1185])).

fof(f1185,plain,
    ( spl8_171
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_171])])).

fof(f462,plain,
    ( spl8_67
  <=> ~ v1_xboole_0(sK4(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f469,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl8_67 ),
    inference(unit_resulting_resolution,[],[f95,f463,f91])).

fof(f463,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK0))))
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f462])).

fof(f1177,plain,
    ( ~ spl8_169
    | ~ spl8_6
    | spl8_67 ),
    inference(avatar_split_clause,[],[f468,f462,f145,f1175])).

fof(f1175,plain,
    ( spl8_169
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_169])])).

fof(f468,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK4(sK0))))
    | ~ spl8_6
    | ~ spl8_67 ),
    inference(unit_resulting_resolution,[],[f146,f463,f91])).

fof(f1162,plain,
    ( ~ spl8_167
    | ~ spl8_150 ),
    inference(avatar_split_clause,[],[f1128,f931,f1160])).

fof(f1160,plain,
    ( spl8_167
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).

fof(f1128,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl8_150 ),
    inference(unit_resulting_resolution,[],[f932,f97])).

fof(f1150,plain,
    ( ~ spl8_165
    | ~ spl8_6
    | spl8_153 ),
    inference(avatar_split_clause,[],[f1102,f934,f145,f1148])).

fof(f1148,plain,
    ( spl8_165
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f934,plain,
    ( spl8_153
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_153])])).

fof(f1102,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_6
    | ~ spl8_153 ),
    inference(unit_resulting_resolution,[],[f935,f207])).

fof(f935,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_153 ),
    inference(avatar_component_clause,[],[f934])).

fof(f1143,plain,
    ( ~ spl8_163
    | spl8_153 ),
    inference(avatar_split_clause,[],[f1098,f934,f1141])).

fof(f1141,plain,
    ( spl8_163
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_163])])).

fof(f1098,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl8_153 ),
    inference(unit_resulting_resolution,[],[f95,f935,f91])).

fof(f1126,plain,
    ( ~ spl8_161
    | ~ spl8_6
    | spl8_159 ),
    inference(avatar_split_clause,[],[f1094,f1083,f145,f1124])).

fof(f1124,plain,
    ( spl8_161
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f1083,plain,
    ( spl8_159
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_159])])).

fof(f1094,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK0))
    | ~ spl8_6
    | ~ spl8_159 ),
    inference(unit_resulting_resolution,[],[f1084,f207])).

fof(f1084,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl8_159 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1088,plain,
    ( spl8_158
    | ~ spl8_156 ),
    inference(avatar_split_clause,[],[f1048,f1017,f1086])).

fof(f1086,plain,
    ( spl8_158
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).

fof(f1017,plain,
    ( spl8_156
  <=> v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f1048,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl8_156 ),
    inference(unit_resulting_resolution,[],[f95,f1018,f91])).

fof(f1018,plain,
    ( v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_156 ),
    inference(avatar_component_clause,[],[f1017])).

fof(f1019,plain,
    ( spl8_156
    | ~ spl8_152 ),
    inference(avatar_split_clause,[],[f1011,f937,f1017])).

fof(f937,plain,
    ( spl8_152
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).

fof(f1011,plain,
    ( v1_xboole_0(sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_152 ),
    inference(unit_resulting_resolution,[],[f944,f262])).

fof(f944,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_152 ),
    inference(unit_resulting_resolution,[],[f233,f938,f118])).

fof(f938,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_152 ),
    inference(avatar_component_clause,[],[f937])).

fof(f1007,plain,
    ( spl8_154
    | ~ spl8_6
    | ~ spl8_20
    | ~ spl8_152 ),
    inference(avatar_split_clause,[],[f975,f937,f200,f145,f1005])).

fof(f1005,plain,
    ( spl8_154
  <=> m1_subset_1(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f975,plain,
    ( m1_subset_1(sK1,o_0_0_xboole_0)
    | ~ spl8_6
    | ~ spl8_20
    | ~ spl8_152 ),
    inference(backward_demodulation,[],[f966,f201])).

fof(f966,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = o_0_0_xboole_0
    | ~ spl8_6
    | ~ spl8_152 ),
    inference(unit_resulting_resolution,[],[f938,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f183,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t6_boole)).

fof(f183,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f146,f94])).

fof(f939,plain,
    ( spl8_150
    | spl8_152
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f263,f200,f937,f931])).

fof(f263,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | r2_hidden(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl8_20 ),
    inference(resolution,[],[f100,f201])).

fof(f924,plain,
    ( spl8_148
    | ~ spl8_118 ),
    inference(avatar_split_clause,[],[f769,f751,f922])).

fof(f751,plain,
    ( spl8_118
  <=> r2_hidden(sK5(sK4(sK7)),sK4(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f769,plain,
    ( m1_subset_1(sK5(sK4(sK7)),k1_zfmisc_1(sK7))
    | ~ spl8_118 ),
    inference(unit_resulting_resolution,[],[f233,f752,f117])).

fof(f752,plain,
    ( r2_hidden(sK5(sK4(sK7)),sK4(sK7))
    | ~ spl8_118 ),
    inference(avatar_component_clause,[],[f751])).

fof(f917,plain,
    ( ~ spl8_147
    | spl8_27 ),
    inference(avatar_split_clause,[],[f766,f230,f915])).

fof(f915,plain,
    ( spl8_147
  <=> ~ r2_hidden(sK4(sK7),sK5(sK4(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f230,plain,
    ( spl8_27
  <=> ~ v1_xboole_0(sK4(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f766,plain,
    ( ~ r2_hidden(sK4(sK7),sK5(sK4(sK7)))
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f231,f539])).

fof(f231,plain,
    ( ~ v1_xboole_0(sK4(sK7))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f230])).

fof(f900,plain,
    ( ~ spl8_145
    | spl8_55 ),
    inference(avatar_split_clause,[],[f386,f365,f898])).

fof(f898,plain,
    ( spl8_145
  <=> ~ r2_hidden(sK7,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f365,plain,
    ( spl8_55
  <=> ~ m1_subset_1(sK7,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f386,plain,
    ( ~ r2_hidden(sK7,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl8_55 ),
    inference(unit_resulting_resolution,[],[f366,f96,f117])).

fof(f366,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f365])).

fof(f891,plain,
    ( ~ spl8_143
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f641,f601,f889])).

fof(f889,plain,
    ( spl8_143
  <=> ~ r2_hidden(sK4(sK0),sK5(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f601,plain,
    ( spl8_88
  <=> r2_hidden(sK5(sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f641,plain,
    ( ~ r2_hidden(sK4(sK0),sK5(sK4(sK0)))
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f602,f97])).

fof(f602,plain,
    ( r2_hidden(sK5(sK4(sK0)),sK4(sK0))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f601])).

fof(f884,plain,
    ( spl8_140
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f636,f601,f882])).

fof(f636,plain,
    ( m1_subset_1(sK5(sK4(sK0)),k1_zfmisc_1(sK0))
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f233,f602,f117])).

fof(f877,plain,
    ( ~ spl8_139
    | spl8_43 ),
    inference(avatar_split_clause,[],[f385,f320,f875])).

fof(f875,plain,
    ( spl8_139
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).

fof(f320,plain,
    ( spl8_43
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f385,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f321,f96,f117])).

fof(f321,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f320])).

fof(f862,plain,
    ( ~ spl8_137
    | ~ spl8_6
    | spl8_123 ),
    inference(avatar_split_clause,[],[f814,f799,f145,f860])).

fof(f860,plain,
    ( spl8_137
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f799,plain,
    ( spl8_123
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).

fof(f814,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK7)))
    | ~ spl8_6
    | ~ spl8_123 ),
    inference(unit_resulting_resolution,[],[f800,f207])).

fof(f800,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK7)))
    | ~ spl8_123 ),
    inference(avatar_component_clause,[],[f799])).

fof(f855,plain,
    ( spl8_134
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f573,f200,f159,f138,f131,f853])).

fof(f853,plain,
    ( spl8_134
  <=> k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f573,plain,
    ( k8_eqrel_1(sK0,sK1) = k7_eqrel_1(sK0,sK1)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f132,f139,f160,f201,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => k8_eqrel_1(X0,X1) = k7_eqrel_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',redefinition_k8_eqrel_1)).

fof(f848,plain,
    ( ~ spl8_133
    | spl8_123 ),
    inference(avatar_split_clause,[],[f810,f799,f846])).

fof(f810,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK7))))
    | ~ spl8_123 ),
    inference(unit_resulting_resolution,[],[f95,f800,f91])).

fof(f841,plain,
    ( ~ spl8_131
    | spl8_127 ),
    inference(avatar_split_clause,[],[f826,f821,f839])).

fof(f839,plain,
    ( spl8_131
  <=> ~ r2_hidden(sK4(sK7),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f821,plain,
    ( spl8_127
  <=> ~ m1_subset_1(sK4(sK7),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).

fof(f826,plain,
    ( ~ r2_hidden(sK4(sK7),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_127 ),
    inference(unit_resulting_resolution,[],[f822,f98])).

fof(f822,plain,
    ( ~ m1_subset_1(sK4(sK7),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_127 ),
    inference(avatar_component_clause,[],[f821])).

fof(f834,plain,
    ( ~ spl8_129
    | spl8_127 ),
    inference(avatar_split_clause,[],[f824,f821,f832])).

fof(f832,plain,
    ( spl8_129
  <=> ~ r2_hidden(sK4(sK7),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f824,plain,
    ( ~ r2_hidden(sK4(sK7),sK4(o_0_0_xboole_0))
    | ~ spl8_127 ),
    inference(unit_resulting_resolution,[],[f233,f822,f117])).

fof(f823,plain,
    ( ~ spl8_127
    | ~ spl8_6
    | ~ spl8_118 ),
    inference(avatar_split_clause,[],[f770,f751,f145,f821])).

fof(f770,plain,
    ( ~ m1_subset_1(sK4(sK7),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_118 ),
    inference(unit_resulting_resolution,[],[f146,f752,f118])).

fof(f808,plain,
    ( ~ spl8_125
    | ~ spl8_6
    | spl8_121 ),
    inference(avatar_split_clause,[],[f792,f784,f145,f806])).

fof(f806,plain,
    ( spl8_125
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).

fof(f792,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK7))
    | ~ spl8_6
    | ~ spl8_121 ),
    inference(unit_resulting_resolution,[],[f785,f207])).

fof(f801,plain,
    ( ~ spl8_123
    | spl8_121 ),
    inference(avatar_split_clause,[],[f788,f784,f799])).

fof(f788,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK7)))
    | ~ spl8_121 ),
    inference(unit_resulting_resolution,[],[f95,f785,f91])).

fof(f786,plain,
    ( ~ spl8_121
    | ~ spl8_118 ),
    inference(avatar_split_clause,[],[f771,f751,f784])).

fof(f771,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK7))
    | ~ spl8_118 ),
    inference(unit_resulting_resolution,[],[f233,f752,f118])).

fof(f753,plain,
    ( spl8_118
    | spl8_27 ),
    inference(avatar_split_clause,[],[f260,f230,f751])).

fof(f260,plain,
    ( r2_hidden(sK5(sK4(sK7)),sK4(sK7))
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f231,f96,f100])).

fof(f746,plain,
    ( spl8_116
    | spl8_9
    | ~ spl8_38
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f737,f619,f299,f152,f744])).

fof(f744,plain,
    ( spl8_116
  <=> v1_funct_1(sK6(sK7,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f152,plain,
    ( spl8_9
  <=> ~ v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f619,plain,
    ( spl8_92
  <=> m2_filter_1(sK6(sK7,sK1),sK7,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f737,plain,
    ( v1_funct_1(sK6(sK7,sK1))
    | ~ spl8_9
    | ~ spl8_38
    | ~ spl8_92 ),
    inference(unit_resulting_resolution,[],[f153,f300,f620,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f620,plain,
    ( m2_filter_1(sK6(sK7,sK1),sK7,sK1)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f619])).

fof(f153,plain,
    ( ~ v1_xboole_0(sK7)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f736,plain,
    ( spl8_114
    | spl8_1
    | ~ spl8_38
    | ~ spl8_90 ),
    inference(avatar_split_clause,[],[f727,f612,f299,f124,f734])).

fof(f734,plain,
    ( spl8_114
  <=> v1_funct_1(sK6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f612,plain,
    ( spl8_90
  <=> m2_filter_1(sK6(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f727,plain,
    ( v1_funct_1(sK6(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_38
    | ~ spl8_90 ),
    inference(unit_resulting_resolution,[],[f125,f300,f613,f101])).

fof(f613,plain,
    ( m2_filter_1(sK6(sK0,sK1),sK0,sK1)
    | ~ spl8_90 ),
    inference(avatar_component_clause,[],[f612])).

fof(f719,plain,
    ( ~ spl8_113
    | ~ spl8_6
    | spl8_101 ),
    inference(avatar_split_clause,[],[f680,f665,f145,f717])).

fof(f717,plain,
    ( spl8_113
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f665,plain,
    ( spl8_101
  <=> ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f680,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(k1_zfmisc_1(sK0)))
    | ~ spl8_6
    | ~ spl8_101 ),
    inference(unit_resulting_resolution,[],[f666,f207])).

fof(f666,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl8_101 ),
    inference(avatar_component_clause,[],[f665])).

fof(f712,plain,
    ( ~ spl8_111
    | spl8_101 ),
    inference(avatar_split_clause,[],[f676,f665,f710])).

fof(f676,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK0))))
    | ~ spl8_101 ),
    inference(unit_resulting_resolution,[],[f95,f666,f91])).

fof(f705,plain,
    ( ~ spl8_109
    | spl8_105 ),
    inference(avatar_split_clause,[],[f691,f686,f703])).

fof(f703,plain,
    ( spl8_109
  <=> ~ r2_hidden(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_109])])).

fof(f686,plain,
    ( spl8_105
  <=> ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f691,plain,
    ( ~ r2_hidden(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_105 ),
    inference(unit_resulting_resolution,[],[f687,f98])).

fof(f687,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_105 ),
    inference(avatar_component_clause,[],[f686])).

fof(f698,plain,
    ( ~ spl8_107
    | spl8_105 ),
    inference(avatar_split_clause,[],[f689,f686,f696])).

fof(f696,plain,
    ( spl8_107
  <=> ~ r2_hidden(sK4(sK0),sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f689,plain,
    ( ~ r2_hidden(sK4(sK0),sK4(o_0_0_xboole_0))
    | ~ spl8_105 ),
    inference(unit_resulting_resolution,[],[f233,f687,f117])).

fof(f688,plain,
    ( ~ spl8_105
    | ~ spl8_6
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f637,f601,f145,f686])).

fof(f637,plain,
    ( ~ m1_subset_1(sK4(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f146,f602,f118])).

fof(f674,plain,
    ( ~ spl8_103
    | ~ spl8_6
    | spl8_99 ),
    inference(avatar_split_clause,[],[f659,f651,f145,f672])).

fof(f672,plain,
    ( spl8_103
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f659,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl8_6
    | ~ spl8_99 ),
    inference(unit_resulting_resolution,[],[f652,f207])).

fof(f667,plain,
    ( ~ spl8_101
    | spl8_99 ),
    inference(avatar_split_clause,[],[f655,f651,f665])).

fof(f655,plain,
    ( ~ v1_xboole_0(sK4(k1_zfmisc_1(sK0)))
    | ~ spl8_99 ),
    inference(unit_resulting_resolution,[],[f95,f652,f91])).

fof(f653,plain,
    ( ~ spl8_99
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f638,f601,f651])).

fof(f638,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl8_88 ),
    inference(unit_resulting_resolution,[],[f233,f602,f118])).

fof(f635,plain,
    ( spl8_96
    | spl8_1
    | ~ spl8_14
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f492,f299,f173,f124,f633])).

fof(f492,plain,
    ( v1_funct_2(sK3,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f125,f300,f174,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f628,plain,
    ( spl8_94
    | spl8_1
    | ~ spl8_12
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f491,f299,f166,f124,f626])).

fof(f491,plain,
    ( v1_funct_2(sK2,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f125,f300,f167,f102])).

fof(f621,plain,
    ( spl8_92
    | spl8_9
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f369,f299,f152,f619])).

fof(f369,plain,
    ( m2_filter_1(sK6(sK7,sK1),sK7,sK1)
    | ~ spl8_9
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f153,f300,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m2_filter_1(sK6(X0,X1),X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m2_filter_1(sK6(X0,X1),X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f49,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_filter_1(X2,X0,X1)
     => m2_filter_1(sK6(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_filter_1(X2,X0,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => ? [X2] : m2_filter_1(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',existence_m2_filter_1)).

fof(f614,plain,
    ( spl8_90
    | spl8_1
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f368,f299,f124,f612])).

fof(f368,plain,
    ( m2_filter_1(sK6(sK0,sK1),sK0,sK1)
    | ~ spl8_1
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f125,f300,f104])).

fof(f603,plain,
    ( spl8_88
    | spl8_23 ),
    inference(avatar_split_clause,[],[f259,f214,f601])).

fof(f214,plain,
    ( spl8_23
  <=> ~ v1_xboole_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f259,plain,
    ( r2_hidden(sK5(sK4(sK0)),sK4(sK0))
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f215,f96,f100])).

fof(f215,plain,
    ( ~ v1_xboole_0(sK4(sK0))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f214])).

fof(f580,plain,
    ( ~ spl8_87
    | ~ spl8_6
    | spl8_83 ),
    inference(avatar_split_clause,[],[f564,f557,f145,f578])).

fof(f578,plain,
    ( spl8_87
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f557,plain,
    ( spl8_83
  <=> ~ v1_xboole_0(k8_eqrel_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f564,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,k8_eqrel_1(sK0,sK1))
    | ~ spl8_6
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f558,f207])).

fof(f558,plain,
    ( ~ v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ spl8_83 ),
    inference(avatar_component_clause,[],[f557])).

fof(f572,plain,
    ( ~ spl8_85
    | spl8_83 ),
    inference(avatar_split_clause,[],[f561,f557,f570])).

fof(f561,plain,
    ( ~ v1_xboole_0(sK4(k8_eqrel_1(sK0,sK1)))
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f95,f558,f91])).

fof(f559,plain,
    ( ~ spl8_83
    | spl8_1
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f552,f548,f124,f557])).

fof(f552,plain,
    ( ~ v1_xboole_0(k8_eqrel_1(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_80 ),
    inference(unit_resulting_resolution,[],[f125,f549,f91])).

fof(f550,plain,
    ( spl8_80
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f543,f200,f159,f138,f131,f548])).

fof(f543,plain,
    ( m1_eqrel_1(k8_eqrel_1(sK0,sK1),sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f132,f139,f160,f201,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_eqrel_1(k8_eqrel_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v3_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v3_relat_2(X1) )
     => m1_eqrel_1(k8_eqrel_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',dt_k8_eqrel_1)).

fof(f527,plain,
    ( ~ spl8_79
    | spl8_55 ),
    inference(avatar_split_clause,[],[f509,f365,f525])).

fof(f525,plain,
    ( spl8_79
  <=> ~ r2_hidden(sK7,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f509,plain,
    ( ~ r2_hidden(sK7,sK4(o_0_0_xboole_0))
    | ~ spl8_55 ),
    inference(unit_resulting_resolution,[],[f366,f233,f117])).

fof(f520,plain,
    ( ~ spl8_77
    | spl8_43 ),
    inference(avatar_split_clause,[],[f508,f320,f518])).

fof(f518,plain,
    ( spl8_77
  <=> ~ r2_hidden(sK0,sK4(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f508,plain,
    ( ~ r2_hidden(sK0,sK4(o_0_0_xboole_0))
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f321,f233,f117])).

fof(f505,plain,
    ( spl8_74
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f498,f488,f503])).

fof(f503,plain,
    ( spl8_74
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f488,plain,
    ( spl8_72
  <=> o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f498,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_72 ),
    inference(superposition,[],[f96,f489])).

fof(f489,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f488])).

fof(f490,plain,
    ( spl8_72
    | ~ spl8_6
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f430,f414,f145,f488])).

fof(f414,plain,
    ( spl8_62
  <=> v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f430,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f415,f185])).

fof(f415,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f414])).

fof(f483,plain,
    ( ~ spl8_71
    | spl8_47 ),
    inference(avatar_split_clause,[],[f376,f335,f481])).

fof(f335,plain,
    ( spl8_47
  <=> ~ v1_xboole_0(sK4(sK4(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f376,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK7))))
    | ~ spl8_47 ),
    inference(unit_resulting_resolution,[],[f95,f336,f91])).

fof(f336,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK7)))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f335])).

fof(f476,plain,
    ( ~ spl8_69
    | ~ spl8_6
    | spl8_47 ),
    inference(avatar_split_clause,[],[f375,f335,f145,f474])).

fof(f474,plain,
    ( spl8_69
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f375,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK7)))
    | ~ spl8_6
    | ~ spl8_47 ),
    inference(unit_resulting_resolution,[],[f146,f336,f91])).

fof(f464,plain,
    ( ~ spl8_67
    | spl8_33 ),
    inference(avatar_split_clause,[],[f304,f254,f462])).

fof(f254,plain,
    ( spl8_33
  <=> ~ v1_xboole_0(sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f304,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK4(sK0))))
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f95,f255,f91])).

fof(f255,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK0)))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f254])).

fof(f457,plain,
    ( ~ spl8_65
    | ~ spl8_6
    | spl8_33 ),
    inference(avatar_split_clause,[],[f303,f254,f145,f455])).

fof(f455,plain,
    ( spl8_65
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f303,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK4(sK0)))
    | ~ spl8_6
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f146,f255,f91])).

fof(f416,plain,
    ( spl8_62
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f402,f145,f414])).

fof(f402,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f96,f314,f100])).

fof(f314,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f146,f96,f118])).

fof(f409,plain,(
    ~ spl8_61 ),
    inference(avatar_split_clause,[],[f89,f407])).

fof(f89,plain,(
    ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( ~ r6_binop_1(k8_eqrel_1(sK0,sK1),k3_filter_1(sK0,sK1,sK2),k3_filter_1(sK0,sK1,sK3))
    & r6_binop_1(sK0,sK2,sK3)
    & m2_filter_1(sK3,sK0,sK1)
    & m2_filter_1(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v8_relat_2(sK1)
    & v3_relat_2(sK1)
    & v1_partfun1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f69,f68,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                    & r6_binop_1(X0,X2,X3)
                    & m2_filter_1(X3,X0,X1) )
                & m2_filter_1(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(sK0,X1),k3_filter_1(sK0,X1,X2),k3_filter_1(sK0,X1,X3))
                  & r6_binop_1(sK0,X2,X3)
                  & m2_filter_1(X3,sK0,X1) )
              & m2_filter_1(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r6_binop_1(k8_eqrel_1(X0,sK1),k3_filter_1(X0,sK1,X2),k3_filter_1(X0,sK1,X3))
                & r6_binop_1(X0,X2,X3)
                & m2_filter_1(X3,X0,sK1) )
            & m2_filter_1(X2,X0,sK1) )
        & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v8_relat_2(sK1)
        & v3_relat_2(sK1)
        & v1_partfun1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
              & r6_binop_1(X0,X2,X3)
              & m2_filter_1(X3,X0,X1) )
          & m2_filter_1(X2,X0,X1) )
     => ( ? [X3] :
            ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,sK2),k3_filter_1(X0,X1,X3))
            & r6_binop_1(X0,sK2,X3)
            & m2_filter_1(X3,X0,X1) )
        & m2_filter_1(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
          & r6_binop_1(X0,X2,X3)
          & m2_filter_1(X3,X0,X1) )
     => ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,sK3))
        & r6_binop_1(X0,X2,sK3)
        & m2_filter_1(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3))
                  & r6_binop_1(X0,X2,X3)
                  & m2_filter_1(X3,X0,X1) )
              & m2_filter_1(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v8_relat_2(X1)
          & v3_relat_2(X1)
          & v1_partfun1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v8_relat_2(X1)
              & v3_relat_2(X1)
              & v1_partfun1(X1,X0) )
           => ! [X2] :
                ( m2_filter_1(X2,X0,X1)
               => ! [X3] :
                    ( m2_filter_1(X3,X0,X1)
                   => ( r6_binop_1(X0,X2,X3)
                     => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v8_relat_2(X1)
            & v3_relat_2(X1)
            & v1_partfun1(X1,X0) )
         => ! [X2] :
              ( m2_filter_1(X2,X0,X1)
             => ! [X3] :
                  ( m2_filter_1(X3,X0,X1)
                 => ( r6_binop_1(X0,X2,X3)
                   => r6_binop_1(k8_eqrel_1(X0,X1),k3_filter_1(X0,X1,X2),k3_filter_1(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',t11_filter_1)).

fof(f395,plain,
    ( ~ spl8_59
    | spl8_55 ),
    inference(avatar_split_clause,[],[f377,f365,f393])).

fof(f393,plain,
    ( spl8_59
  <=> ~ r2_hidden(sK7,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f377,plain,
    ( ~ r2_hidden(sK7,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_55 ),
    inference(unit_resulting_resolution,[],[f366,f98])).

fof(f384,plain,
    ( ~ spl8_57
    | spl8_43 ),
    inference(avatar_split_clause,[],[f323,f320,f382])).

fof(f382,plain,
    ( spl8_57
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f323,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_43 ),
    inference(unit_resulting_resolution,[],[f321,f98])).

fof(f367,plain,
    ( ~ spl8_55
    | ~ spl8_6
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f313,f283,f145,f365])).

fof(f283,plain,
    ( spl8_36
  <=> r2_hidden(sK5(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f313,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f284,f146,f118])).

fof(f284,plain,
    ( r2_hidden(sK5(sK7),sK7)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f283])).

fof(f360,plain,
    ( spl8_52
    | spl8_1
    | ~ spl8_14
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f346,f299,f173,f124,f358])).

fof(f346,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1
    | ~ spl8_14
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f125,f300,f174,f101])).

fof(f353,plain,
    ( spl8_50
    | spl8_1
    | ~ spl8_12
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f345,f299,f166,f124,f351])).

fof(f345,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f125,f300,f167,f101])).

fof(f344,plain,
    ( ~ spl8_49
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f288,f283,f342])).

fof(f342,plain,
    ( spl8_49
  <=> ~ r2_hidden(sK7,sK5(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f288,plain,
    ( ~ r2_hidden(sK7,sK5(sK7))
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f284,f97])).

fof(f337,plain,
    ( ~ spl8_47
    | spl8_27 ),
    inference(avatar_split_clause,[],[f242,f230,f335])).

fof(f242,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK7)))
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f95,f231,f91])).

fof(f330,plain,
    ( ~ spl8_45
    | ~ spl8_6
    | spl8_27 ),
    inference(avatar_split_clause,[],[f241,f230,f145,f328])).

fof(f328,plain,
    ( spl8_45
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f241,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK7))
    | ~ spl8_6
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f146,f231,f91])).

fof(f322,plain,
    ( ~ spl8_43
    | ~ spl8_6
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f312,f269,f145,f320])).

fof(f269,plain,
    ( spl8_34
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f312,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_6
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f270,f146,f118])).

fof(f270,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f269])).

fof(f311,plain,
    ( ~ spl8_41
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f274,f269,f309])).

fof(f309,plain,
    ( spl8_41
  <=> ~ r2_hidden(sK0,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f274,plain,
    ( ~ r2_hidden(sK0,sK5(sK0))
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f270,f97])).

fof(f301,plain,
    ( spl8_38
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f294,f200,f299])).

fof(f294,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f201,f113])).

fof(f285,plain,
    ( spl8_36
    | spl8_9 ),
    inference(avatar_split_clause,[],[f258,f152,f283])).

fof(f258,plain,
    ( r2_hidden(sK5(sK7),sK7)
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f153,f96,f100])).

fof(f271,plain,
    ( spl8_34
    | spl8_1 ),
    inference(avatar_split_clause,[],[f257,f124,f269])).

fof(f257,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f125,f96,f100])).

fof(f256,plain,
    ( ~ spl8_33
    | spl8_23 ),
    inference(avatar_split_clause,[],[f225,f214,f254])).

fof(f225,plain,
    ( ~ v1_xboole_0(sK4(sK4(sK0)))
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f95,f215,f91])).

fof(f249,plain,
    ( ~ spl8_31
    | ~ spl8_6
    | spl8_23 ),
    inference(avatar_split_clause,[],[f224,f214,f145,f247])).

fof(f247,plain,
    ( spl8_31
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f224,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK4(sK0))
    | ~ spl8_6
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f146,f215,f91])).

fof(f240,plain,
    ( ~ spl8_29
    | ~ spl8_6
    | spl8_9 ),
    inference(avatar_split_clause,[],[f206,f152,f145,f238])).

fof(f238,plain,
    ( spl8_29
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f206,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK7)
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f153,f146,f91])).

fof(f232,plain,
    ( ~ spl8_27
    | spl8_9 ),
    inference(avatar_split_clause,[],[f204,f152,f230])).

fof(f204,plain,
    ( ~ v1_xboole_0(sK4(sK7))
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f153,f95,f91])).

fof(f223,plain,
    ( ~ spl8_25
    | spl8_1
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f205,f145,f124,f221])).

fof(f221,plain,
    ( spl8_25
  <=> ~ m1_eqrel_1(o_0_0_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f205,plain,
    ( ~ m1_eqrel_1(o_0_0_xboole_0,sK0)
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f125,f146,f91])).

fof(f216,plain,
    ( ~ spl8_23
    | spl8_1 ),
    inference(avatar_split_clause,[],[f203,f124,f214])).

fof(f203,plain,
    ( ~ v1_xboole_0(sK4(sK0))
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f125,f95,f91])).

fof(f202,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f85,f200])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f70])).

fof(f192,plain,
    ( spl8_18
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f183,f145,f190])).

fof(f190,plain,
    ( spl8_18
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f182,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f88,f180])).

fof(f88,plain,(
    r6_binop_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f175,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f87,f173])).

fof(f87,plain,(
    m2_filter_1(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f168,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f86,f166])).

fof(f86,plain,(
    m2_filter_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f161,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f82,f159])).

fof(f82,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f154,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f119,f152])).

fof(f119,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ~ v1_xboole_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f79])).

fof(f79,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK7) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',rc7_funct_1)).

fof(f147,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f90,f145])).

fof(f90,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t11_filter_1.p',dt_o_0_0_xboole_0)).

fof(f140,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f84,f138])).

fof(f84,plain,(
    v8_relat_2(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f133,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f83,f131])).

fof(f83,plain,(
    v3_relat_2(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f126,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f81,f124])).

fof(f81,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
