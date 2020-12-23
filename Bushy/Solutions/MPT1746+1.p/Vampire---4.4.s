%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t55_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:17 EDT 2019

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  904 (3371 expanded)
%              Number of leaves         :  230 (1374 expanded)
%              Depth                    :   20
%              Number of atoms          : 3397 (13212 expanded)
%              Number of equality atoms :   89 ( 377 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2339,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f120,f127,f134,f141,f148,f155,f162,f169,f176,f183,f191,f204,f211,f227,f237,f250,f267,f278,f285,f307,f348,f355,f362,f369,f379,f393,f402,f423,f439,f465,f478,f498,f510,f532,f539,f558,f565,f572,f586,f600,f613,f621,f622,f642,f651,f669,f688,f693,f694,f707,f717,f729,f743,f762,f775,f777,f786,f787,f810,f824,f837,f845,f858,f868,f884,f893,f900,f907,f908,f921,f928,f935,f942,f955,f962,f969,f986,f1003,f1013,f1021,f1029,f1039,f1047,f1061,f1071,f1079,f1093,f1103,f1111,f1125,f1144,f1151,f1158,f1172,f1186,f1199,f1206,f1217,f1223,f1239,f1246,f1253,f1254,f1264,f1265,f1284,f1298,f1317,f1329,f1345,f1372,f1380,f1391,f1399,f1407,f1414,f1433,f1447,f1468,f1474,f1497,f1523,f1534,f1542,f1550,f1557,f1581,f1590,f1604,f1618,f1635,f1644,f1658,f1673,f1689,f1703,f1716,f1725,f1730,f1743,f1756,f1811,f1884,f1905,f1919,f1937,f1945,f1952,f1959,f1980,f1984,f1988,f1998,f2005,f2007,f2021,f2069,f2078,f2091,f2104,f2118,f2157,f2174,f2181,f2188,f2193,f2231,f2245,f2267,f2287,f2301,f2322,f2326,f2330,f2338])).

fof(f2338,plain,
    ( spl9_178
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1256,f193,f1123])).

fof(f1123,plain,
    ( spl9_178
  <=> v5_pre_topc(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_178])])).

fof(f193,plain,
    ( spl9_24
  <=> sP0(sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f1256,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ spl9_24 ),
    inference(resolution,[],[f194,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v5_pre_topc(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,X1,X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(X2,X1,X0)
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(X2,X0,X1)
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(X2) )
      & ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f194,plain,
    ( sP0(sK2,sK1,sK3)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f193])).

fof(f2330,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_26
    | spl9_29
    | ~ spl9_178 ),
    inference(avatar_contradiction_clause,[],[f2329])).

fof(f2329,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_26
    | ~ spl9_29
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f2327,f203])).

fof(f203,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl9_26
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f2327,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_29
    | ~ spl9_178 ),
    inference(resolution,[],[f2315,f210])).

fof(f210,plain,
    ( ~ r1_tmap_1(sK1,sK2,sK3,sK4)
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl9_29
  <=> ~ r1_tmap_1(sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f2315,plain,
    ( ! [X2] :
        ( r1_tmap_1(sK1,sK2,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f2314,f154])).

fof(f154,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl9_12
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2314,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK2,sK3,X2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f2313,f182])).

fof(f182,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl9_20
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f2313,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK2,sK3,X2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f2310,f190])).

fof(f190,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl9_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f2310,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK2,sK3,X2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_178 ),
    inference(resolution,[],[f1485,f1124])).

fof(f1124,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ spl9_178 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1485,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK1,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK2,X0,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1484,f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f1484,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK1,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK2,X0,X1) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1482,f126])).

fof(f126,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl9_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1482,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK1,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK2,X0,X1) )
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f1086,f119])).

fof(f119,plain,
    ( v2_pre_topc(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl9_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f1086,plain,
    ( ! [X4,X5,X3] :
        ( ~ v2_pre_topc(X4)
        | ~ v5_pre_topc(X5,X4,sK2)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK2))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK2))
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X3,u1_struct_0(X4))
        | v2_struct_0(X4)
        | r1_tmap_1(X4,sK2,X5,X3) )
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1085,f133])).

fof(f133,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_7
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f1085,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(X4))
        | ~ v5_pre_topc(X5,X4,sK2)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK2))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK2))
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | r1_tmap_1(X4,sK2,X5,X3)
        | v2_struct_0(sK2) )
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1082,f147])).

fof(f147,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl9_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f1082,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(X4))
        | ~ v5_pre_topc(X5,X4,sK2)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK2))))
        | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(sK2))
        | ~ v1_funct_1(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | v2_struct_0(X4)
        | ~ l1_pre_topc(sK2)
        | r1_tmap_1(X4,sK2,X5,X3)
        | v2_struct_0(sK2) )
    | ~ spl9_8 ),
    inference(resolution,[],[f90,f140])).

fof(f140,plain,
    ( v2_pre_topc(sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl9_8
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tmap_1(X1,X0,X2,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK5(X0,X1,X2))
                    & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t49_tmap_1)).

fof(f2326,plain,
    ( spl9_364
    | spl9_372
    | ~ spl9_360 ),
    inference(avatar_split_clause,[],[f2257,f2243,f2324,f2279])).

fof(f2279,plain,
    ( spl9_364
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_364])])).

fof(f2324,plain,
    ( spl9_372
  <=> ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_372])])).

fof(f2243,plain,
    ( spl9_360
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_360])])).

fof(f2257,plain,
    ( ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3))) )
    | ~ spl9_360 ),
    inference(superposition,[],[f289,f2244])).

fof(f2244,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl9_360 ),
    inference(avatar_component_clause,[],[f2243])).

fof(f289,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f103,f213])).

fof(f213,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f96,f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',existence_m1_subset_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t2_subset)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t4_subset)).

fof(f2322,plain,
    ( ~ spl9_371
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_366 ),
    inference(avatar_split_clause,[],[f2307,f2285,f235,f225,f2320])).

fof(f2320,plain,
    ( spl9_371
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_371])])).

fof(f225,plain,
    ( spl9_30
  <=> v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f235,plain,
    ( spl9_32
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f2285,plain,
    ( spl9_366
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_366])])).

fof(f2307,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_366 ),
    inference(forward_demodulation,[],[f2302,f236])).

fof(f236,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f235])).

fof(f2302,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(sK3)),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_366 ),
    inference(resolution,[],[f2286,f228])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0)))) )
    | ~ spl9_30 ),
    inference(resolution,[],[f226,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t5_subset)).

fof(f226,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f225])).

fof(f2286,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl9_366 ),
    inference(avatar_component_clause,[],[f2285])).

fof(f2301,plain,
    ( spl9_368
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_364 ),
    inference(avatar_split_clause,[],[f2292,f2279,f235,f225,f2299])).

fof(f2299,plain,
    ( spl9_368
  <=> k1_zfmisc_1(k1_zfmisc_1(sK3)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_368])])).

fof(f2292,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK3)) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_364 ),
    inference(forward_demodulation,[],[f2288,f236])).

fof(f2288,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK3)) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_364 ),
    inference(resolution,[],[f2280,f229])).

fof(f229,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK6(k1_zfmisc_1(o_0_0_xboole_0)) = X2 )
    | ~ spl9_30 ),
    inference(resolution,[],[f226,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t8_boole)).

fof(f2280,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl9_364 ),
    inference(avatar_component_clause,[],[f2279])).

fof(f2287,plain,
    ( spl9_364
    | spl9_366
    | ~ spl9_360 ),
    inference(avatar_split_clause,[],[f2259,f2243,f2285,f2279])).

fof(f2259,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl9_360 ),
    inference(superposition,[],[f213,f2244])).

fof(f2267,plain,
    ( spl9_362
    | ~ spl9_360 ),
    inference(avatar_split_clause,[],[f2260,f2243,f2265])).

fof(f2265,plain,
    ( spl9_362
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_362])])).

fof(f2260,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl9_360 ),
    inference(superposition,[],[f93,f2244])).

fof(f2245,plain,
    ( spl9_360
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_356 ),
    inference(avatar_split_clause,[],[f2236,f2223,f235,f225,f2243])).

fof(f2223,plain,
    ( spl9_356
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_356])])).

fof(f2236,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_356 ),
    inference(forward_demodulation,[],[f2232,f236])).

fof(f2232,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK6(k1_zfmisc_1(k1_zfmisc_1(sK3)))
    | ~ spl9_30
    | ~ spl9_356 ),
    inference(resolution,[],[f2224,f229])).

fof(f2224,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))))
    | ~ spl9_356 ),
    inference(avatar_component_clause,[],[f2223])).

fof(f2231,plain,
    ( spl9_354
    | spl9_356
    | spl9_358
    | ~ spl9_22
    | spl9_83 ),
    inference(avatar_split_clause,[],[f2210,f553,f189,f2229,f2223,f2217])).

fof(f2217,plain,
    ( spl9_354
  <=> m1_subset_1(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_354])])).

fof(f2229,plain,
    ( spl9_358
  <=> v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_358])])).

fof(f553,plain,
    ( spl9_83
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f2210,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3)))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))))
    | m1_subset_1(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_22
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f2198,f554])).

fof(f554,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_83 ),
    inference(avatar_component_clause,[],[f553])).

fof(f2198,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3)))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))))
    | v1_xboole_0(sK3)
    | m1_subset_1(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_22 ),
    inference(resolution,[],[f1835,f190])).

fof(f1835,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X1)))))
      | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X1)
      | m1_subset_1(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X1))))),X2) ) ),
    inference(resolution,[],[f1559,f103])).

fof(f1559,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X0))))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(X0)))))
      | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(X0)))) ) ),
    inference(resolution,[],[f309,f93])).

fof(f309,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | v1_xboole_0(X2)
      | r2_hidden(sK6(sK6(X1)),X2)
      | v1_xboole_0(sK6(X1))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f291,f289])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r2_hidden(sK6(X0),X1) ) ),
    inference(resolution,[],[f289,f96])).

fof(f2193,plain,
    ( spl9_346
    | spl9_352
    | ~ spl9_342 ),
    inference(avatar_split_clause,[],[f2147,f2116,f2191,f2166])).

fof(f2166,plain,
    ( spl9_346
  <=> v1_xboole_0(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_346])])).

fof(f2191,plain,
    ( spl9_352
  <=> ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_352])])).

fof(f2116,plain,
    ( spl9_342
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_342])])).

fof(f2147,plain,
    ( ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))) )
    | ~ spl9_342 ),
    inference(superposition,[],[f289,f2117])).

fof(f2117,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_342 ),
    inference(avatar_component_clause,[],[f2116])).

fof(f2188,plain,
    ( ~ spl9_351
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_348 ),
    inference(avatar_split_clause,[],[f2180,f2172,f235,f225,f2186])).

fof(f2186,plain,
    ( spl9_351
  <=> ~ m1_subset_1(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_351])])).

fof(f2172,plain,
    ( spl9_348
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_348])])).

fof(f2180,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_348 ),
    inference(forward_demodulation,[],[f2175,f236])).

fof(f2175,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_348 ),
    inference(resolution,[],[f2173,f228])).

fof(f2173,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_348 ),
    inference(avatar_component_clause,[],[f2172])).

fof(f2181,plain,
    ( ~ spl9_347
    | ~ spl9_348 ),
    inference(avatar_split_clause,[],[f2179,f2172,f2163])).

fof(f2163,plain,
    ( spl9_347
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_347])])).

fof(f2179,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_348 ),
    inference(resolution,[],[f2173,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t7_boole)).

fof(f2174,plain,
    ( spl9_346
    | spl9_348
    | ~ spl9_342 ),
    inference(avatar_split_clause,[],[f2149,f2116,f2172,f2166])).

fof(f2149,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | v1_xboole_0(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_342 ),
    inference(superposition,[],[f213,f2117])).

fof(f2157,plain,
    ( spl9_344
    | ~ spl9_342 ),
    inference(avatar_split_clause,[],[f2150,f2116,f2155])).

fof(f2155,plain,
    ( spl9_344
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_344])])).

fof(f2150,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_342 ),
    inference(superposition,[],[f93,f2117])).

fof(f2118,plain,
    ( spl9_342
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_340 ),
    inference(avatar_split_clause,[],[f2109,f2102,f235,f225,f2116])).

fof(f2102,plain,
    ( spl9_340
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_340])])).

fof(f2109,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_340 ),
    inference(forward_demodulation,[],[f2105,f236])).

fof(f2105,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_30
    | ~ spl9_340 ),
    inference(resolution,[],[f2103,f229])).

fof(f2103,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))))
    | ~ spl9_340 ),
    inference(avatar_component_clause,[],[f2102])).

fof(f2104,plain,
    ( spl9_338
    | spl9_340
    | ~ spl9_104
    | spl9_185
    | spl9_253 ),
    inference(avatar_split_clause,[],[f2056,f1576,f1139,f705,f2102,f2096])).

fof(f2096,plain,
    ( spl9_338
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_338])])).

fof(f705,plain,
    ( spl9_104
  <=> m1_subset_1(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f1139,plain,
    ( spl9_185
  <=> ~ v1_xboole_0(sK7(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_185])])).

fof(f1576,plain,
    ( spl9_253
  <=> ~ v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_253])])).

fof(f2056,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_104
    | ~ spl9_185
    | ~ spl9_253 ),
    inference(subsumption_resolution,[],[f2055,f1577])).

fof(f1577,plain,
    ( ~ v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK1))))
    | ~ spl9_253 ),
    inference(avatar_component_clause,[],[f1576])).

fof(f2055,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK1))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_104
    | ~ spl9_185 ),
    inference(subsumption_resolution,[],[f2048,f1140])).

fof(f1140,plain,
    ( ~ v1_xboole_0(sK7(sK1,sK1))
    | ~ spl9_185 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f2048,plain,
    ( v1_xboole_0(sK7(sK1,sK1))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK1))))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1))))))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_104 ),
    inference(resolution,[],[f1813,f706])).

fof(f706,plain,
    ( m1_subset_1(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl9_104 ),
    inference(avatar_component_clause,[],[f705])).

fof(f1813,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK6(k1_zfmisc_1(X1)))
      | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X1)))))
      | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X1))))),X2) ) ),
    inference(resolution,[],[f1776,f103])).

fof(f1776,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X0))))),X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X0)))))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f623,f96])).

fof(f623,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X0))))),X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(X0))))) ) ),
    inference(resolution,[],[f316,f93])).

fof(f316,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(sK6(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | m1_subset_1(sK6(sK6(k1_zfmisc_1(X1))),X2) ) ),
    inference(resolution,[],[f308,f103])).

fof(f308,plain,(
    ! [X0] :
      ( r2_hidden(sK6(sK6(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK6(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f291,f93])).

fof(f2091,plain,
    ( ~ spl9_337
    | ~ spl9_334 ),
    inference(avatar_split_clause,[],[f2082,f2076,f2089])).

fof(f2089,plain,
    ( spl9_337
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_337])])).

fof(f2076,plain,
    ( spl9_334
  <=> r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_334])])).

fof(f2082,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))))
    | ~ spl9_334 ),
    inference(resolution,[],[f2077,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',antisymmetry_r2_hidden)).

fof(f2077,plain,
    ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_334 ),
    inference(avatar_component_clause,[],[f2076])).

fof(f2078,plain,
    ( spl9_334
    | spl9_81
    | ~ spl9_330 ),
    inference(avatar_split_clause,[],[f2071,f2061,f547,f2076])).

fof(f547,plain,
    ( spl9_81
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f2061,plain,
    ( spl9_330
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_330])])).

fof(f2071,plain,
    ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_81
    | ~ spl9_330 ),
    inference(subsumption_resolution,[],[f2070,f548])).

fof(f548,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_81 ),
    inference(avatar_component_clause,[],[f547])).

fof(f2070,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_330 ),
    inference(resolution,[],[f2062,f96])).

fof(f2062,plain,
    ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_330 ),
    inference(avatar_component_clause,[],[f2061])).

fof(f2069,plain,
    ( spl9_330
    | spl9_332
    | spl9_96
    | ~ spl9_22
    | spl9_83 ),
    inference(avatar_split_clause,[],[f2054,f553,f189,f640,f2067,f2061])).

fof(f2067,plain,
    ( spl9_332
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_332])])).

fof(f640,plain,
    ( spl9_96
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f2054,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK3)))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3)))))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_22
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f2042,f554])).

fof(f2042,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(sK6(k1_zfmisc_1(sK3)))
    | v1_xboole_0(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3)))))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK6(k1_zfmisc_1(sK3))))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_22 ),
    inference(resolution,[],[f1813,f190])).

fof(f2021,plain,
    ( spl9_302
    | spl9_328
    | spl9_304
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f1566,f235,f225,f1900,f2019,f1894])).

fof(f1894,plain,
    ( spl9_302
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_302])])).

fof(f2019,plain,
    ( spl9_328
  <=> v1_xboole_0(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_328])])).

fof(f1900,plain,
    ( spl9_304
  <=> v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_304])])).

fof(f1566,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
    | v1_xboole_0(sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(resolution,[],[f334,f93])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | v1_xboole_0(sK6(X0))
        | v1_xboole_0(sK6(sK6(X0)))
        | v1_xboole_0(X0) )
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(resolution,[],[f299,f289])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
        | v1_xboole_0(sK6(X0))
        | v1_xboole_0(X0) )
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(resolution,[],[f296,f289])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f294,f236])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
        | v1_xboole_0(X0) )
    | ~ spl9_30 ),
    inference(resolution,[],[f228,f213])).

fof(f2007,plain,
    ( ~ spl9_152
    | spl9_327 ),
    inference(avatar_contradiction_clause,[],[f2006])).

fof(f2006,plain,
    ( $false
    | ~ spl9_152
    | ~ spl9_327 ),
    inference(subsumption_resolution,[],[f2000,f1002])).

fof(f1002,plain,
    ( sP0(sK1,sK1,sK7(sK1,sK1))
    | ~ spl9_152 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f1001,plain,
    ( spl9_152
  <=> sP0(sK1,sK1,sK7(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_152])])).

fof(f2000,plain,
    ( ~ sP0(sK1,sK1,sK7(sK1,sK1))
    | ~ spl9_327 ),
    inference(resolution,[],[f1997,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1997,plain,
    ( ~ v1_funct_2(sK7(sK1,sK1),u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl9_327 ),
    inference(avatar_component_clause,[],[f1996])).

fof(f1996,plain,
    ( spl9_327
  <=> ~ v1_funct_2(sK7(sK1,sK1),u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_327])])).

fof(f2005,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_327 ),
    inference(avatar_contradiction_clause,[],[f2004])).

fof(f2004,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_327 ),
    inference(subsumption_resolution,[],[f2003,f112])).

fof(f2003,plain,
    ( v2_struct_0(sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_327 ),
    inference(subsumption_resolution,[],[f2002,f119])).

fof(f2002,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_4
    | ~ spl9_327 ),
    inference(subsumption_resolution,[],[f2001,f126])).

fof(f2001,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_327 ),
    inference(duplicate_literal_removal,[],[f1999])).

fof(f1999,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl9_327 ),
    inference(resolution,[],[f1997,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK7(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( v5_pre_topc(sK7(X0,X1),X0,X1)
        & v1_funct_2(sK7(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
     => ( v5_pre_topc(sK7(X0,X1),X0,X1)
        & v1_funct_2(sK7(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & v4_relat_1(X2,u1_struct_0(X0))
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X2] :
          ( v5_pre_topc(X2,X0,X1)
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2)
          & v5_relat_1(X2,u1_struct_0(X1))
          & v4_relat_1(X2,u1_struct_0(X0))
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',rc8_pre_topc)).

fof(f1998,plain,
    ( spl9_324
    | ~ spl9_327
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_104
    | ~ spl9_154
    | ~ spl9_156 ),
    inference(avatar_split_clause,[],[f1965,f1019,f1011,f705,f125,f118,f111,f1996,f1990])).

fof(f1990,plain,
    ( spl9_324
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK1,sK7(sK1,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_324])])).

fof(f1011,plain,
    ( spl9_154
  <=> v1_funct_1(sK7(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_154])])).

fof(f1019,plain,
    ( spl9_156
  <=> v5_pre_topc(sK7(sK1,sK1),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).

fof(f1965,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK7(sK1,sK1),u1_struct_0(sK1),u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK1,sK7(sK1,sK1),X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_104
    | ~ spl9_154
    | ~ spl9_156 ),
    inference(subsumption_resolution,[],[f1964,f1012])).

fof(f1012,plain,
    ( v1_funct_1(sK7(sK1,sK1))
    | ~ spl9_154 ),
    inference(avatar_component_clause,[],[f1011])).

fof(f1964,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK7(sK1,sK1),u1_struct_0(sK1),u1_struct_0(sK1))
        | ~ v1_funct_1(sK7(sK1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK1,sK7(sK1,sK1),X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_104
    | ~ spl9_156 ),
    inference(subsumption_resolution,[],[f1961,f706])).

fof(f1961,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK7(sK1,sK1),u1_struct_0(sK1),u1_struct_0(sK1))
        | ~ v1_funct_1(sK7(sK1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK1,sK7(sK1,sK1),X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_156 ),
    inference(resolution,[],[f1326,f1020])).

fof(f1020,plain,
    ( v5_pre_topc(sK7(sK1,sK1),sK1,sK1)
    | ~ spl9_156 ),
    inference(avatar_component_clause,[],[f1019])).

fof(f1326,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK1,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK1,X0,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1325,f112])).

fof(f1325,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK1,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK1,X0,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1323,f126])).

fof(f1323,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,sK1,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK1,X0,X1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f1084,f119])).

fof(f1084,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ v5_pre_topc(X2,X1,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | r1_tmap_1(X1,sK1,X2,X0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1083,f112])).

fof(f1083,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v5_pre_topc(X2,X1,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | r1_tmap_1(X1,sK1,X2,X0)
        | v2_struct_0(sK1) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1081,f126])).

fof(f1081,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v5_pre_topc(X2,X1,sK1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK1)
        | r1_tmap_1(X1,sK1,X2,X0)
        | v2_struct_0(sK1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f90,f119])).

fof(f1988,plain,
    ( spl9_302
    | spl9_322
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f1927,f1917,f1986,f1894])).

fof(f1986,plain,
    ( spl9_322
  <=> ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_322])])).

fof(f1917,plain,
    ( spl9_308
  <=> o_0_0_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_308])])).

fof(f1927,plain,
    ( ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),k1_zfmisc_1(X0))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) )
    | ~ spl9_308 ),
    inference(superposition,[],[f289,f1918])).

fof(f1918,plain,
    ( o_0_0_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_308 ),
    inference(avatar_component_clause,[],[f1917])).

fof(f1984,plain,
    ( spl9_316
    | spl9_320
    | ~ spl9_312 ),
    inference(avatar_split_clause,[],[f1967,f1943,f1982,f1972])).

fof(f1972,plain,
    ( spl9_316
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_316])])).

fof(f1982,plain,
    ( spl9_320
  <=> ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_320])])).

fof(f1943,plain,
    ( spl9_312
  <=> r2_hidden(o_0_0_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_312])])).

fof(f1967,plain,
    ( ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) )
    | ~ spl9_312 ),
    inference(resolution,[],[f1947,f289])).

fof(f1947,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),k1_zfmisc_1(X0))
        | m1_subset_1(o_0_0_xboole_0,X0) )
    | ~ spl9_312 ),
    inference(resolution,[],[f1944,f103])).

fof(f1944,plain,
    ( r2_hidden(o_0_0_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_312 ),
    inference(avatar_component_clause,[],[f1943])).

fof(f1980,plain,
    ( spl9_316
    | ~ spl9_319
    | spl9_315 ),
    inference(avatar_split_clause,[],[f1960,f1957,f1978,f1972])).

fof(f1978,plain,
    ( spl9_319
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_319])])).

fof(f1957,plain,
    ( spl9_315
  <=> ~ m1_subset_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_315])])).

fof(f1960,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_315 ),
    inference(resolution,[],[f1958,f289])).

fof(f1958,plain,
    ( ~ m1_subset_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_315 ),
    inference(avatar_component_clause,[],[f1957])).

fof(f1959,plain,
    ( ~ spl9_315
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_312 ),
    inference(avatar_split_clause,[],[f1951,f1943,f235,f225,f1957])).

fof(f1951,plain,
    ( ~ m1_subset_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_312 ),
    inference(forward_demodulation,[],[f1946,f236])).

fof(f1946,plain,
    ( ~ m1_subset_1(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_312 ),
    inference(resolution,[],[f1944,f228])).

fof(f1952,plain,
    ( ~ spl9_303
    | ~ spl9_312 ),
    inference(avatar_split_clause,[],[f1950,f1943,f1891])).

fof(f1891,plain,
    ( spl9_303
  <=> ~ v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_303])])).

fof(f1950,plain,
    ( ~ v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_312 ),
    inference(resolution,[],[f1944,f102])).

fof(f1945,plain,
    ( spl9_302
    | spl9_312
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f1929,f1917,f1943,f1894])).

fof(f1929,plain,
    ( r2_hidden(o_0_0_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_308 ),
    inference(superposition,[],[f213,f1918])).

fof(f1937,plain,
    ( spl9_310
    | ~ spl9_308 ),
    inference(avatar_split_clause,[],[f1930,f1917,f1935])).

fof(f1935,plain,
    ( spl9_310
  <=> m1_subset_1(o_0_0_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_310])])).

fof(f1930,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_308 ),
    inference(superposition,[],[f93,f1918])).

fof(f1919,plain,
    ( spl9_308
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_304 ),
    inference(avatar_split_clause,[],[f1910,f1900,f235,f225,f1917])).

fof(f1910,plain,
    ( o_0_0_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_304 ),
    inference(forward_demodulation,[],[f1906,f236])).

fof(f1906,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_30
    | ~ spl9_304 ),
    inference(resolution,[],[f1901,f229])).

fof(f1901,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
    | ~ spl9_304 ),
    inference(avatar_component_clause,[],[f1900])).

fof(f1905,plain,
    ( spl9_302
    | spl9_304
    | spl9_306
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f1563,f160,f1903,f1900,f1894])).

fof(f1903,plain,
    ( spl9_306
  <=> ! [X0] : ~ r2_hidden(X0,sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_306])])).

fof(f160,plain,
    ( spl9_14
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f1563,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK6(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))))
        | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))))
        | v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) )
    | ~ spl9_14 ),
    inference(resolution,[],[f314,f93])).

fof(f314,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X2,sK6(sK6(X1)))
        | v1_xboole_0(sK6(X1))
        | v1_xboole_0(X1) )
    | ~ spl9_14 ),
    inference(resolution,[],[f292,f289])).

fof(f292,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
        | v1_xboole_0(X2)
        | ~ r2_hidden(X3,sK6(X2)) )
    | ~ spl9_14 ),
    inference(resolution,[],[f289,f218])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl9_14 ),
    inference(resolution,[],[f104,f161])).

fof(f161,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1884,plain,
    ( spl9_296
    | ~ spl9_299
    | spl9_300
    | ~ spl9_101
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(avatar_split_clause,[],[f1461,f1445,f153,f146,f139,f132,f125,f118,f111,f664,f1882,f1876,f1870])).

fof(f1870,plain,
    ( spl9_296
  <=> v5_pre_topc(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_296])])).

fof(f1876,plain,
    ( spl9_299
  <=> ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_299])])).

fof(f1882,plain,
    ( spl9_300
  <=> m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_300])])).

fof(f664,plain,
    ( spl9_101
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).

fof(f1445,plain,
    ( spl9_234
  <=> k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_234])])).

fof(f1461,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK3,sK2,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(subsumption_resolution,[],[f1460,f112])).

fof(f1460,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK3,sK2,sK1)
    | v2_struct_0(sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(subsumption_resolution,[],[f1459,f119])).

fof(f1459,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK3,sK2,sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(subsumption_resolution,[],[f1458,f126])).

fof(f1458,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK3,sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(subsumption_resolution,[],[f1457,f133])).

fof(f1457,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK3,sK2,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(subsumption_resolution,[],[f1456,f140])).

fof(f1456,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK3,sK2,sK1)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(subsumption_resolution,[],[f1455,f147])).

fof(f1455,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK3,sK2,sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_12
    | ~ spl9_234 ),
    inference(superposition,[],[f885,f1446])).

fof(f1446,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl9_234 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f885,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | m1_subset_1(sK5(X0,X1,sK3),u1_struct_0(X1))
        | ~ v1_funct_2(sK3,u1_struct_0(X1),u1_struct_0(X0))
        | v5_pre_topc(sK3,X1,X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_12 ),
    inference(resolution,[],[f91,f154])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | v5_pre_topc(X2,X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1811,plain,
    ( spl9_290
    | ~ spl9_293
    | spl9_294
    | ~ spl9_101
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_210 ),
    inference(avatar_split_clause,[],[f1310,f1296,f153,f146,f139,f132,f664,f1809,f1803,f1797])).

fof(f1797,plain,
    ( spl9_290
  <=> v5_pre_topc(sK3,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_290])])).

fof(f1803,plain,
    ( spl9_293
  <=> ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_293])])).

fof(f1809,plain,
    ( spl9_294
  <=> m1_subset_1(sK5(sK2,sK2,sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_294])])).

fof(f1296,plain,
    ( spl9_210
  <=> k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).

fof(f1310,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK2,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK2)
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_210 ),
    inference(subsumption_resolution,[],[f1309,f133])).

fof(f1309,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK2,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK2)
    | v2_struct_0(sK2)
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_210 ),
    inference(subsumption_resolution,[],[f1308,f140])).

fof(f1308,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK2,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_210 ),
    inference(subsumption_resolution,[],[f1307,f147])).

fof(f1307,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK2,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_12
    | ~ spl9_210 ),
    inference(duplicate_literal_removal,[],[f1306])).

fof(f1306,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | m1_subset_1(sK5(sK2,sK2,sK3),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_12
    | ~ spl9_210 ),
    inference(superposition,[],[f885,f1297])).

fof(f1297,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)) = o_0_0_xboole_0
    | ~ spl9_210 ),
    inference(avatar_component_clause,[],[f1296])).

fof(f1756,plain,
    ( spl9_286
    | spl9_232
    | spl9_288
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f869,f866,f1754,f1431,f1748])).

fof(f1748,plain,
    ( spl9_286
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK2,sK1)))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_286])])).

fof(f1431,plain,
    ( spl9_232
  <=> v1_xboole_0(sK7(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_232])])).

fof(f1754,plain,
    ( spl9_288
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_288])])).

fof(f866,plain,
    ( spl9_126
  <=> m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f869,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK2,sK1))))
    | v1_xboole_0(sK7(sK2,sK1))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK2,sK1)))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl9_126 ),
    inference(resolution,[],[f867,f316])).

fof(f867,plain,
    ( m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_126 ),
    inference(avatar_component_clause,[],[f866])).

fof(f1743,plain,
    ( spl9_282
    | spl9_208
    | spl9_284
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f859,f856,f1741,f1282,f1735])).

fof(f1735,plain,
    ( spl9_282
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK2,sK2)))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_282])])).

fof(f1282,plain,
    ( spl9_208
  <=> v1_xboole_0(sK7(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_208])])).

fof(f1741,plain,
    ( spl9_284
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_284])])).

fof(f856,plain,
    ( spl9_124
  <=> m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f859,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK2,sK2))))
    | v1_xboole_0(sK7(sK2,sK2))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK2,sK2)))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ spl9_124 ),
    inference(resolution,[],[f857,f316])).

fof(f857,plain,
    ( m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f856])).

fof(f1730,plain,
    ( spl9_270
    | spl9_280
    | ~ spl9_266 ),
    inference(avatar_split_clause,[],[f1663,f1656,f1728,f1681])).

fof(f1681,plain,
    ( spl9_270
  <=> v1_xboole_0(k1_zfmisc_1(sK7(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_270])])).

fof(f1728,plain,
    ( spl9_280
  <=> ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(sK7(sK1,sK2)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_280])])).

fof(f1656,plain,
    ( spl9_266
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK7(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_266])])).

fof(f1663,plain,
    ( ! [X0] :
        ( m1_subset_1(o_0_0_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(sK7(sK1,sK2)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(sK7(sK1,sK2))) )
    | ~ spl9_266 ),
    inference(superposition,[],[f289,f1657])).

fof(f1657,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK7(sK1,sK2)))
    | ~ spl9_266 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f1725,plain,
    ( ~ spl9_279
    | spl9_261
    | ~ spl9_266 ),
    inference(avatar_split_clause,[],[f1718,f1656,f1624,f1723])).

fof(f1723,plain,
    ( spl9_279
  <=> ~ m1_subset_1(sK6(o_0_0_xboole_0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_279])])).

fof(f1624,plain,
    ( spl9_261
  <=> ~ m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_261])])).

fof(f1718,plain,
    ( ~ m1_subset_1(sK6(o_0_0_xboole_0),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_261
    | ~ spl9_266 ),
    inference(superposition,[],[f1625,f1657])).

fof(f1625,plain,
    ( ~ m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_261 ),
    inference(avatar_component_clause,[],[f1624])).

fof(f1716,plain,
    ( ~ spl9_277
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_272 ),
    inference(avatar_split_clause,[],[f1709,f1687,f235,f225,f1714])).

fof(f1714,plain,
    ( spl9_277
  <=> ~ m1_subset_1(k1_zfmisc_1(sK7(sK1,sK2)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_277])])).

fof(f1687,plain,
    ( spl9_272
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK7(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_272])])).

fof(f1709,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK7(sK1,sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_272 ),
    inference(forward_demodulation,[],[f1704,f236])).

fof(f1704,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK7(sK1,sK2)),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_272 ),
    inference(resolution,[],[f1688,f228])).

fof(f1688,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK7(sK1,sK2)))
    | ~ spl9_272 ),
    inference(avatar_component_clause,[],[f1687])).

fof(f1703,plain,
    ( spl9_274
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_270 ),
    inference(avatar_split_clause,[],[f1694,f1681,f235,f225,f1701])).

fof(f1701,plain,
    ( spl9_274
  <=> k1_zfmisc_1(sK7(sK1,sK2)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_274])])).

fof(f1694,plain,
    ( k1_zfmisc_1(sK7(sK1,sK2)) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_270 ),
    inference(forward_demodulation,[],[f1690,f236])).

fof(f1690,plain,
    ( k1_zfmisc_1(sK7(sK1,sK2)) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_270 ),
    inference(resolution,[],[f1682,f229])).

fof(f1682,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK7(sK1,sK2)))
    | ~ spl9_270 ),
    inference(avatar_component_clause,[],[f1681])).

fof(f1689,plain,
    ( spl9_270
    | spl9_272
    | ~ spl9_266 ),
    inference(avatar_split_clause,[],[f1665,f1656,f1687,f1681])).

fof(f1665,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(sK7(sK1,sK2)))
    | v1_xboole_0(k1_zfmisc_1(sK7(sK1,sK2)))
    | ~ spl9_266 ),
    inference(superposition,[],[f213,f1657])).

fof(f1673,plain,
    ( spl9_268
    | ~ spl9_266 ),
    inference(avatar_split_clause,[],[f1666,f1656,f1671])).

fof(f1671,plain,
    ( spl9_268
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK7(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_268])])).

fof(f1666,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK7(sK1,sK2)))
    | ~ spl9_266 ),
    inference(superposition,[],[f93,f1657])).

fof(f1658,plain,
    ( spl9_266
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_262 ),
    inference(avatar_split_clause,[],[f1649,f1633,f235,f225,f1656])).

fof(f1633,plain,
    ( spl9_262
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_262])])).

fof(f1649,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK7(sK1,sK2)))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_262 ),
    inference(forward_demodulation,[],[f1645,f236])).

fof(f1645,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK6(k1_zfmisc_1(sK7(sK1,sK2)))
    | ~ spl9_30
    | ~ spl9_262 ),
    inference(resolution,[],[f1634,f229])).

fof(f1634,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK2))))
    | ~ spl9_262 ),
    inference(avatar_component_clause,[],[f1633])).

fof(f1644,plain,
    ( spl9_264
    | spl9_81
    | ~ spl9_260 ),
    inference(avatar_split_clause,[],[f1637,f1627,f547,f1642])).

fof(f1642,plain,
    ( spl9_264
  <=> r2_hidden(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_264])])).

fof(f1627,plain,
    ( spl9_260
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_260])])).

fof(f1637,plain,
    ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_81
    | ~ spl9_260 ),
    inference(subsumption_resolution,[],[f1636,f548])).

fof(f1636,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_260 ),
    inference(resolution,[],[f1628,f96])).

fof(f1628,plain,
    ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_260 ),
    inference(avatar_component_clause,[],[f1627])).

fof(f1635,plain,
    ( spl9_260
    | spl9_116
    | spl9_262
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f718,f715,f1633,f773,f1627])).

fof(f773,plain,
    ( spl9_116
  <=> v1_xboole_0(sK7(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f715,plain,
    ( spl9_106
  <=> m1_subset_1(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f718,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK2))))
    | v1_xboole_0(sK7(sK1,sK2))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK2)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_106 ),
    inference(resolution,[],[f716,f316])).

fof(f716,plain,
    ( m1_subset_1(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f715])).

fof(f1618,plain,
    ( ~ spl9_259
    | ~ spl9_254 ),
    inference(avatar_split_clause,[],[f1609,f1588,f1616])).

fof(f1616,plain,
    ( spl9_259
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_259])])).

fof(f1588,plain,
    ( spl9_254
  <=> r2_hidden(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_254])])).

fof(f1609,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))))
    | ~ spl9_254 ),
    inference(resolution,[],[f1589,f94])).

fof(f1589,plain,
    ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_254 ),
    inference(avatar_component_clause,[],[f1588])).

fof(f1604,plain,
    ( spl9_256
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_252 ),
    inference(avatar_split_clause,[],[f1595,f1579,f235,f225,f1602])).

fof(f1602,plain,
    ( spl9_256
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK7(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_256])])).

fof(f1579,plain,
    ( spl9_252
  <=> v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_252])])).

fof(f1595,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(sK7(sK1,sK1)))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_252 ),
    inference(forward_demodulation,[],[f1591,f236])).

fof(f1591,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK6(k1_zfmisc_1(sK7(sK1,sK1)))
    | ~ spl9_30
    | ~ spl9_252 ),
    inference(resolution,[],[f1580,f229])).

fof(f1580,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK1))))
    | ~ spl9_252 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f1590,plain,
    ( spl9_254
    | spl9_183
    | ~ spl9_250 ),
    inference(avatar_split_clause,[],[f1583,f1573,f1133,f1588])).

fof(f1133,plain,
    ( spl9_183
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_183])])).

fof(f1573,plain,
    ( spl9_250
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_250])])).

fof(f1583,plain,
    ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_183
    | ~ spl9_250 ),
    inference(subsumption_resolution,[],[f1582,f1134])).

fof(f1134,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_183 ),
    inference(avatar_component_clause,[],[f1133])).

fof(f1582,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | r2_hidden(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_250 ),
    inference(resolution,[],[f1574,f96])).

fof(f1574,plain,
    ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_250 ),
    inference(avatar_component_clause,[],[f1573])).

fof(f1581,plain,
    ( spl9_250
    | spl9_184
    | spl9_252
    | ~ spl9_104 ),
    inference(avatar_split_clause,[],[f708,f705,f1579,f1142,f1573])).

fof(f1142,plain,
    ( spl9_184
  <=> v1_xboole_0(sK7(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_184])])).

fof(f708,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK7(sK1,sK1))))
    | v1_xboole_0(sK7(sK1,sK1))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK7(sK1,sK1)))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_104 ),
    inference(resolution,[],[f706,f316])).

fof(f1557,plain,
    ( spl9_248
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_238 ),
    inference(avatar_split_clause,[],[f1516,f1495,f146,f139,f125,f118,f111,f1555])).

fof(f1555,plain,
    ( spl9_248
  <=> v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).

fof(f1495,plain,
    ( spl9_238
  <=> o_0_0_xboole_0 = sK7(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_238])])).

fof(f1516,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_238 ),
    inference(subsumption_resolution,[],[f1515,f140])).

fof(f1515,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_238 ),
    inference(subsumption_resolution,[],[f1514,f147])).

fof(f1514,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_238 ),
    inference(subsumption_resolution,[],[f1513,f112])).

fof(f1513,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_238 ),
    inference(subsumption_resolution,[],[f1512,f119])).

fof(f1512,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_4
    | ~ spl9_238 ),
    inference(subsumption_resolution,[],[f1507,f126])).

fof(f1507,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_238 ),
    inference(superposition,[],[f99,f1496])).

fof(f1496,plain,
    ( o_0_0_xboole_0 = sK7(sK2,sK1)
    | ~ spl9_238 ),
    inference(avatar_component_clause,[],[f1495])).

fof(f1550,plain,
    ( ~ spl9_247
    | spl9_149
    | ~ spl9_234 ),
    inference(avatar_split_clause,[],[f1452,f1445,f967,f1548])).

fof(f1548,plain,
    ( spl9_247
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK7(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_247])])).

fof(f967,plain,
    ( spl9_149
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),sK7(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).

fof(f1452,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK7(sK2,sK1))
    | ~ spl9_149
    | ~ spl9_234 ),
    inference(superposition,[],[f968,f1446])).

fof(f968,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),sK7(sK2,sK1))
    | ~ spl9_149 ),
    inference(avatar_component_clause,[],[f967])).

fof(f1542,plain,
    ( spl9_244
    | ~ spl9_144
    | ~ spl9_234 ),
    inference(avatar_split_clause,[],[f1449,f1445,f947,f1540])).

fof(f1540,plain,
    ( spl9_244
  <=> r2_hidden(sK7(sK2,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).

fof(f947,plain,
    ( spl9_144
  <=> r2_hidden(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f1449,plain,
    ( r2_hidden(sK7(sK2,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_144
    | ~ spl9_234 ),
    inference(superposition,[],[f948,f1446])).

fof(f948,plain,
    ( r2_hidden(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_144 ),
    inference(avatar_component_clause,[],[f947])).

fof(f1534,plain,
    ( spl9_242
    | ~ spl9_174
    | ~ spl9_238 ),
    inference(avatar_split_clause,[],[f1503,f1495,f1109,f1532])).

fof(f1532,plain,
    ( spl9_242
  <=> v5_pre_topc(o_0_0_xboole_0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_242])])).

fof(f1109,plain,
    ( spl9_174
  <=> v5_pre_topc(sK7(sK2,sK1),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_174])])).

fof(f1503,plain,
    ( v5_pre_topc(o_0_0_xboole_0,sK2,sK1)
    | ~ spl9_174
    | ~ spl9_238 ),
    inference(superposition,[],[f1110,f1496])).

fof(f1110,plain,
    ( v5_pre_topc(sK7(sK2,sK1),sK2,sK1)
    | ~ spl9_174 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1523,plain,
    ( spl9_240
    | ~ spl9_170
    | ~ spl9_238 ),
    inference(avatar_split_clause,[],[f1501,f1495,f1091,f1521])).

fof(f1521,plain,
    ( spl9_240
  <=> sP0(sK1,sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_240])])).

fof(f1091,plain,
    ( spl9_170
  <=> sP0(sK1,sK2,sK7(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_170])])).

fof(f1501,plain,
    ( sP0(sK1,sK2,o_0_0_xboole_0)
    | ~ spl9_170
    | ~ spl9_238 ),
    inference(superposition,[],[f1092,f1496])).

fof(f1092,plain,
    ( sP0(sK1,sK2,sK7(sK2,sK1))
    | ~ spl9_170 ),
    inference(avatar_component_clause,[],[f1091])).

fof(f1497,plain,
    ( spl9_238
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_232 ),
    inference(avatar_split_clause,[],[f1479,f1431,f235,f225,f1495])).

fof(f1479,plain,
    ( o_0_0_xboole_0 = sK7(sK2,sK1)
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_232 ),
    inference(forward_demodulation,[],[f1475,f236])).

fof(f1475,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK7(sK2,sK1)
    | ~ spl9_30
    | ~ spl9_232 ),
    inference(resolution,[],[f1432,f229])).

fof(f1432,plain,
    ( v1_xboole_0(sK7(sK2,sK1))
    | ~ spl9_232 ),
    inference(avatar_component_clause,[],[f1431])).

fof(f1474,plain,
    ( spl9_232
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_236 ),
    inference(avatar_split_clause,[],[f1469,f1466,f235,f225,f1431])).

fof(f1466,plain,
    ( spl9_236
  <=> m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_236])])).

fof(f1469,plain,
    ( v1_xboole_0(sK7(sK2,sK1))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_236 ),
    inference(resolution,[],[f1467,f296])).

fof(f1467,plain,
    ( m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_236 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1468,plain,
    ( spl9_236
    | ~ spl9_126
    | ~ spl9_234 ),
    inference(avatar_split_clause,[],[f1448,f1445,f866,f1466])).

fof(f1448,plain,
    ( m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_126
    | ~ spl9_234 ),
    inference(superposition,[],[f867,f1446])).

fof(f1447,plain,
    ( spl9_234
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_230 ),
    inference(avatar_split_clause,[],[f1438,f1425,f235,f225,f1445])).

fof(f1425,plain,
    ( spl9_230
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_230])])).

fof(f1438,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_230 ),
    inference(forward_demodulation,[],[f1434,f236])).

fof(f1434,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_230 ),
    inference(resolution,[],[f1426,f229])).

fof(f1426,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl9_230 ),
    inference(avatar_component_clause,[],[f1425])).

fof(f1433,plain,
    ( spl9_228
    | spl9_230
    | spl9_232
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f870,f866,f1431,f1425,f1419])).

fof(f1419,plain,
    ( spl9_228
  <=> r2_hidden(sK6(sK7(sK2,sK1)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_228])])).

fof(f870,plain,
    ( v1_xboole_0(sK7(sK2,sK1))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | r2_hidden(sK6(sK7(sK2,sK1)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))
    | ~ spl9_126 ),
    inference(resolution,[],[f867,f291])).

fof(f1414,plain,
    ( spl9_226
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_214 ),
    inference(avatar_split_clause,[],[f1365,f1343,f146,f139,f132,f1412])).

fof(f1412,plain,
    ( spl9_226
  <=> v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_226])])).

fof(f1343,plain,
    ( spl9_214
  <=> o_0_0_xboole_0 = sK7(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_214])])).

fof(f1365,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_214 ),
    inference(subsumption_resolution,[],[f1364,f133])).

fof(f1364,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_214 ),
    inference(subsumption_resolution,[],[f1363,f140])).

fof(f1363,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_10
    | ~ spl9_214 ),
    inference(subsumption_resolution,[],[f1360,f147])).

fof(f1360,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_214 ),
    inference(duplicate_literal_removal,[],[f1355])).

fof(f1355,plain,
    ( v1_funct_2(o_0_0_xboole_0,u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_214 ),
    inference(superposition,[],[f99,f1344])).

fof(f1344,plain,
    ( o_0_0_xboole_0 = sK7(sK2,sK2)
    | ~ spl9_214 ),
    inference(avatar_component_clause,[],[f1343])).

fof(f1407,plain,
    ( ~ spl9_225
    | spl9_141
    | ~ spl9_210 ),
    inference(avatar_split_clause,[],[f1303,f1296,f933,f1405])).

fof(f1405,plain,
    ( spl9_225
  <=> ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK7(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_225])])).

fof(f933,plain,
    ( spl9_141
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))),sK7(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_141])])).

fof(f1303,plain,
    ( ~ r2_hidden(k1_zfmisc_1(o_0_0_xboole_0),sK7(sK2,sK2))
    | ~ spl9_141
    | ~ spl9_210 ),
    inference(superposition,[],[f934,f1297])).

fof(f934,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))),sK7(sK2,sK2))
    | ~ spl9_141 ),
    inference(avatar_component_clause,[],[f933])).

fof(f1399,plain,
    ( spl9_222
    | ~ spl9_136
    | ~ spl9_210 ),
    inference(avatar_split_clause,[],[f1300,f1296,f913,f1397])).

fof(f1397,plain,
    ( spl9_222
  <=> r2_hidden(sK7(sK2,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_222])])).

fof(f913,plain,
    ( spl9_136
  <=> r2_hidden(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1300,plain,
    ( r2_hidden(sK7(sK2,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_136
    | ~ spl9_210 ),
    inference(superposition,[],[f914,f1297])).

fof(f914,plain,
    ( r2_hidden(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f913])).

fof(f1391,plain,
    ( spl9_220
    | ~ spl9_168
    | ~ spl9_214 ),
    inference(avatar_split_clause,[],[f1351,f1343,f1077,f1389])).

fof(f1389,plain,
    ( spl9_220
  <=> v5_pre_topc(o_0_0_xboole_0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_220])])).

fof(f1077,plain,
    ( spl9_168
  <=> v5_pre_topc(sK7(sK2,sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_168])])).

fof(f1351,plain,
    ( v5_pre_topc(o_0_0_xboole_0,sK2,sK2)
    | ~ spl9_168
    | ~ spl9_214 ),
    inference(superposition,[],[f1078,f1344])).

fof(f1078,plain,
    ( v5_pre_topc(sK7(sK2,sK2),sK2,sK2)
    | ~ spl9_168 ),
    inference(avatar_component_clause,[],[f1077])).

fof(f1380,plain,
    ( spl9_218
    | ~ spl9_164
    | ~ spl9_214 ),
    inference(avatar_split_clause,[],[f1349,f1343,f1059,f1378])).

fof(f1378,plain,
    ( spl9_218
  <=> sP0(sK2,sK2,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_218])])).

fof(f1059,plain,
    ( spl9_164
  <=> sP0(sK2,sK2,sK7(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_164])])).

fof(f1349,plain,
    ( sP0(sK2,sK2,o_0_0_xboole_0)
    | ~ spl9_164
    | ~ spl9_214 ),
    inference(superposition,[],[f1060,f1344])).

fof(f1060,plain,
    ( sP0(sK2,sK2,sK7(sK2,sK2))
    | ~ spl9_164 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1372,plain,
    ( spl9_216
    | ~ spl9_166
    | ~ spl9_214 ),
    inference(avatar_split_clause,[],[f1350,f1343,f1069,f1370])).

fof(f1370,plain,
    ( spl9_216
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_216])])).

fof(f1069,plain,
    ( spl9_166
  <=> v1_funct_1(sK7(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_166])])).

fof(f1350,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl9_166
    | ~ spl9_214 ),
    inference(superposition,[],[f1070,f1344])).

fof(f1070,plain,
    ( v1_funct_1(sK7(sK2,sK2))
    | ~ spl9_166 ),
    inference(avatar_component_clause,[],[f1069])).

fof(f1345,plain,
    ( spl9_214
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_208 ),
    inference(avatar_split_clause,[],[f1334,f1282,f235,f225,f1343])).

fof(f1334,plain,
    ( o_0_0_xboole_0 = sK7(sK2,sK2)
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_208 ),
    inference(forward_demodulation,[],[f1330,f236])).

fof(f1330,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK7(sK2,sK2)
    | ~ spl9_30
    | ~ spl9_208 ),
    inference(resolution,[],[f1283,f229])).

fof(f1283,plain,
    ( v1_xboole_0(sK7(sK2,sK2))
    | ~ spl9_208 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f1329,plain,
    ( spl9_208
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_212 ),
    inference(avatar_split_clause,[],[f1318,f1315,f235,f225,f1282])).

fof(f1315,plain,
    ( spl9_212
  <=> m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_212])])).

fof(f1318,plain,
    ( v1_xboole_0(sK7(sK2,sK2))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_212 ),
    inference(resolution,[],[f1316,f296])).

fof(f1316,plain,
    ( m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_212 ),
    inference(avatar_component_clause,[],[f1315])).

fof(f1317,plain,
    ( spl9_212
    | ~ spl9_124
    | ~ spl9_210 ),
    inference(avatar_split_clause,[],[f1299,f1296,f856,f1315])).

fof(f1299,plain,
    ( m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_124
    | ~ spl9_210 ),
    inference(superposition,[],[f857,f1297])).

fof(f1298,plain,
    ( spl9_210
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_206 ),
    inference(avatar_split_clause,[],[f1289,f1276,f235,f225,f1296])).

fof(f1276,plain,
    ( spl9_206
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_206])])).

fof(f1289,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_206 ),
    inference(forward_demodulation,[],[f1285,f236])).

fof(f1285,plain,
    ( k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_206 ),
    inference(resolution,[],[f1277,f229])).

fof(f1277,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ spl9_206 ),
    inference(avatar_component_clause,[],[f1276])).

fof(f1284,plain,
    ( spl9_204
    | spl9_206
    | spl9_208
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f860,f856,f1282,f1276,f1270])).

fof(f1270,plain,
    ( spl9_204
  <=> r2_hidden(sK6(sK7(sK2,sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_204])])).

fof(f860,plain,
    ( v1_xboole_0(sK7(sK2,sK2))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | r2_hidden(sK6(sK7(sK2,sK2)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ spl9_124 ),
    inference(resolution,[],[f857,f291])).

fof(f1265,plain,
    ( spl9_114
    | spl9_80
    | spl9_116
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f719,f715,f773,f550,f767])).

fof(f767,plain,
    ( spl9_114
  <=> r2_hidden(sK6(sK7(sK1,sK2)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f550,plain,
    ( spl9_80
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f719,plain,
    ( v1_xboole_0(sK7(sK1,sK2))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK6(sK7(sK1,sK2)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_106 ),
    inference(resolution,[],[f716,f291])).

fof(f1264,plain,
    ( ~ spl9_203
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_196 ),
    inference(avatar_split_clause,[],[f1245,f1231,f235,f225,f1262])).

fof(f1262,plain,
    ( spl9_203
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_203])])).

fof(f1231,plain,
    ( spl9_196
  <=> r2_hidden(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_196])])).

fof(f1245,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_196 ),
    inference(forward_demodulation,[],[f1240,f236])).

fof(f1240,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_196 ),
    inference(resolution,[],[f1232,f228])).

fof(f1232,plain,
    ( r2_hidden(sK4,u1_struct_0(sK1))
    | ~ spl9_196 ),
    inference(avatar_component_clause,[],[f1231])).

fof(f1254,plain,
    ( spl9_24
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_178 ),
    inference(avatar_split_clause,[],[f1225,f1123,f189,f181,f153,f193])).

fof(f1225,plain,
    ( sP0(sK2,sK1,sK3)
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f1224,f154])).

fof(f1224,plain,
    ( sP0(sK2,sK1,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f1219,f182])).

fof(f1219,plain,
    ( sP0(sK2,sK1,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ spl9_22
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f1218,f190])).

fof(f1218,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | sP0(sK2,sK1,sK3)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ spl9_178 ),
    inference(resolution,[],[f1124,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | sP0(X0,X1,X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1253,plain,
    ( ~ spl9_201
    | ~ spl9_196 ),
    inference(avatar_split_clause,[],[f1243,f1231,f1251])).

fof(f1251,plain,
    ( spl9_201
  <=> ~ r2_hidden(u1_struct_0(sK1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_201])])).

fof(f1243,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK4)
    | ~ spl9_196 ),
    inference(resolution,[],[f1232,f94])).

fof(f1246,plain,
    ( ~ spl9_199
    | ~ spl9_196 ),
    inference(avatar_split_clause,[],[f1244,f1231,f1234])).

fof(f1234,plain,
    ( spl9_199
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_199])])).

fof(f1244,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_196 ),
    inference(resolution,[],[f1232,f102])).

fof(f1239,plain,
    ( spl9_196
    | spl9_198
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f1226,f202,f1237,f1231])).

fof(f1237,plain,
    ( spl9_198
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_198])])).

fof(f1226,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK4,u1_struct_0(sK1))
    | ~ spl9_26 ),
    inference(resolution,[],[f203,f96])).

fof(f1223,plain,
    ( ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | spl9_25
    | ~ spl9_178 ),
    inference(avatar_contradiction_clause,[],[f1222])).

fof(f1222,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f1221,f154])).

fof(f1221,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f1220,f182])).

fof(f1220,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ spl9_22
    | ~ spl9_25
    | ~ spl9_178 ),
    inference(subsumption_resolution,[],[f1219,f197])).

fof(f197,plain,
    ( ~ sP0(sK2,sK1,sK3)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl9_25
  <=> ~ sP0(sK2,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f1217,plain,
    ( spl9_178
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | spl9_177 ),
    inference(avatar_split_clause,[],[f1216,f1117,f189,f181,f153,f146,f139,f132,f125,f118,f111,f1123])).

fof(f1117,plain,
    ( spl9_177
  <=> ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_177])])).

fof(f1216,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1215,f133])).

fof(f1215,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v2_struct_0(sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1214,f140])).

fof(f1214,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1213,f147])).

fof(f1213,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1212,f112])).

fof(f1212,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1211,f119])).

fof(f1211,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1210,f126])).

fof(f1210,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1209,f182])).

fof(f1209,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_12
    | ~ spl9_22
    | ~ spl9_177 ),
    inference(subsumption_resolution,[],[f1208,f1118])).

fof(f1118,plain,
    ( ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_177 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1208,plain,
    ( m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_12
    | ~ spl9_22 ),
    inference(resolution,[],[f885,f190])).

fof(f1206,plain,
    ( ~ spl9_195
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_180 ),
    inference(avatar_split_clause,[],[f1150,f1130,f235,f225,f1204])).

fof(f1204,plain,
    ( spl9_195
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_195])])).

fof(f1130,plain,
    ( spl9_180
  <=> r2_hidden(sK6(sK7(sK1,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_180])])).

fof(f1150,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_180 ),
    inference(forward_demodulation,[],[f1145,f236])).

fof(f1145,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_180 ),
    inference(resolution,[],[f1131,f228])).

fof(f1131,plain,
    ( r2_hidden(sK6(sK7(sK1,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_180 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1199,plain,
    ( ~ spl9_193
    | ~ spl9_180 ),
    inference(avatar_split_clause,[],[f1148,f1130,f1197])).

fof(f1197,plain,
    ( spl9_193
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK6(sK7(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_193])])).

fof(f1148,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),sK6(sK7(sK1,sK1)))
    | ~ spl9_180 ),
    inference(resolution,[],[f1131,f94])).

fof(f1186,plain,
    ( spl9_190
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_184 ),
    inference(avatar_split_clause,[],[f1177,f1142,f235,f225,f1184])).

fof(f1184,plain,
    ( spl9_190
  <=> o_0_0_xboole_0 = sK7(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_190])])).

fof(f1177,plain,
    ( o_0_0_xboole_0 = sK7(sK1,sK1)
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_184 ),
    inference(forward_demodulation,[],[f1173,f236])).

fof(f1173,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK7(sK1,sK1)
    | ~ spl9_30
    | ~ spl9_184 ),
    inference(resolution,[],[f1143,f229])).

fof(f1143,plain,
    ( v1_xboole_0(sK7(sK1,sK1))
    | ~ spl9_184 ),
    inference(avatar_component_clause,[],[f1142])).

fof(f1172,plain,
    ( spl9_188
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_182 ),
    inference(avatar_split_clause,[],[f1163,f1136,f235,f225,f1170])).

fof(f1170,plain,
    ( spl9_188
  <=> k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_188])])).

fof(f1136,plain,
    ( spl9_182
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_182])])).

fof(f1163,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_182 ),
    inference(forward_demodulation,[],[f1159,f236])).

fof(f1159,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_182 ),
    inference(resolution,[],[f1137,f229])).

fof(f1137,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_182 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f1158,plain,
    ( spl9_186
    | ~ spl9_180 ),
    inference(avatar_split_clause,[],[f1147,f1130,f1156])).

fof(f1156,plain,
    ( spl9_186
  <=> m1_subset_1(sK6(sK7(sK1,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_186])])).

fof(f1147,plain,
    ( m1_subset_1(sK6(sK7(sK1,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_180 ),
    inference(resolution,[],[f1131,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t1_subset)).

fof(f1151,plain,
    ( ~ spl9_183
    | ~ spl9_180 ),
    inference(avatar_split_clause,[],[f1149,f1130,f1133])).

fof(f1149,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_180 ),
    inference(resolution,[],[f1131,f102])).

fof(f1144,plain,
    ( spl9_180
    | spl9_182
    | spl9_184
    | ~ spl9_104 ),
    inference(avatar_split_clause,[],[f709,f705,f1142,f1136,f1130])).

fof(f709,plain,
    ( v1_xboole_0(sK7(sK1,sK1))
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | r2_hidden(sK6(sK7(sK1,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | ~ spl9_104 ),
    inference(resolution,[],[f706,f291])).

fof(f1125,plain,
    ( ~ spl9_177
    | spl9_178
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f979,f276,f189,f181,f153,f146,f139,f132,f125,f118,f111,f1123,f1117])).

fof(f276,plain,
    ( spl9_40
  <=> ! [X4] :
        ( r1_tmap_1(sK1,sK2,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f979,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f978,f133])).

fof(f978,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f977,f140])).

fof(f977,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f976,f147])).

fof(f976,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f975,f112])).

fof(f975,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f974,f119])).

fof(f974,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f973,f126])).

fof(f973,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f972,f154])).

fof(f972,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_20
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f971,f182])).

fof(f971,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(subsumption_resolution,[],[f970,f190])).

fof(f970,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK5(sK2,sK1,sK3),u1_struct_0(sK1))
    | ~ spl9_40 ),
    inference(resolution,[],[f92,f277])).

fof(f277,plain,
    ( ! [X4] :
        ( r1_tmap_1(sK1,sK2,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f276])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,sK5(X0,X1,X2))
      | v5_pre_topc(X2,X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1111,plain,
    ( spl9_174
    | ~ spl9_170 ),
    inference(avatar_split_clause,[],[f1095,f1091,f1109])).

fof(f1095,plain,
    ( v5_pre_topc(sK7(sK2,sK1),sK2,sK1)
    | ~ spl9_170 ),
    inference(resolution,[],[f1092,f72])).

fof(f1103,plain,
    ( spl9_172
    | ~ spl9_170 ),
    inference(avatar_split_clause,[],[f1096,f1091,f1101])).

fof(f1101,plain,
    ( spl9_172
  <=> v1_funct_1(sK7(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_172])])).

fof(f1096,plain,
    ( v1_funct_1(sK7(sK2,sK1))
    | ~ spl9_170 ),
    inference(resolution,[],[f1092,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1093,plain,
    ( spl9_170
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f1052,f146,f139,f125,f118,f111,f1091])).

fof(f1052,plain,
    ( sP0(sK1,sK2,sK7(sK2,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1051,f112])).

fof(f1051,plain,
    ( v2_struct_0(sK1)
    | sP0(sK1,sK2,sK7(sK2,sK1))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1049,f126])).

fof(f1049,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sP0(sK1,sK2,sK7(sK2,sK1))
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f990,f119])).

fof(f990,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | sP0(X1,sK2,sK7(sK2,X1)) )
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f988,f147])).

fof(f988,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK2)
        | sP0(X1,sK2,sK7(sK2,X1)) )
    | ~ spl9_8 ),
    inference(resolution,[],[f791,f140])).

fof(f791,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | sP0(X1,X0,sK7(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f790,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK7(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f790,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,sK7(X0,X1))
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f789,f99])).

fof(f789,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,sK7(X0,X1))
      | ~ v1_funct_2(sK7(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f788,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f788,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP0(X1,X0,sK7(X0,X1))
      | ~ v1_funct_2(sK7(X0,X1),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(sK7(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f74,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(sK7(X0,X1),X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1079,plain,
    ( spl9_168
    | ~ spl9_164 ),
    inference(avatar_split_clause,[],[f1063,f1059,f1077])).

fof(f1063,plain,
    ( v5_pre_topc(sK7(sK2,sK2),sK2,sK2)
    | ~ spl9_164 ),
    inference(resolution,[],[f1060,f72])).

fof(f1071,plain,
    ( spl9_166
    | ~ spl9_164 ),
    inference(avatar_split_clause,[],[f1064,f1059,f1069])).

fof(f1064,plain,
    ( v1_funct_1(sK7(sK2,sK2))
    | ~ spl9_164 ),
    inference(resolution,[],[f1060,f70])).

fof(f1061,plain,
    ( spl9_164
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f1054,f146,f139,f132,f1059])).

fof(f1054,plain,
    ( sP0(sK2,sK2,sK7(sK2,sK2))
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1053,f133])).

fof(f1053,plain,
    ( v2_struct_0(sK2)
    | sP0(sK2,sK2,sK7(sK2,sK2))
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f1050,f147])).

fof(f1050,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | sP0(sK2,sK2,sK7(sK2,sK2))
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f990,f140])).

fof(f1047,plain,
    ( spl9_162
    | ~ spl9_158 ),
    inference(avatar_split_clause,[],[f1031,f1027,f1045])).

fof(f1045,plain,
    ( spl9_162
  <=> v5_pre_topc(sK7(sK1,sK2),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f1027,plain,
    ( spl9_158
  <=> sP0(sK2,sK1,sK7(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_158])])).

fof(f1031,plain,
    ( v5_pre_topc(sK7(sK1,sK2),sK1,sK2)
    | ~ spl9_158 ),
    inference(resolution,[],[f1028,f72])).

fof(f1028,plain,
    ( sP0(sK2,sK1,sK7(sK1,sK2))
    | ~ spl9_158 ),
    inference(avatar_component_clause,[],[f1027])).

fof(f1039,plain,
    ( spl9_160
    | ~ spl9_158 ),
    inference(avatar_split_clause,[],[f1032,f1027,f1037])).

fof(f1037,plain,
    ( spl9_160
  <=> v1_funct_1(sK7(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_160])])).

fof(f1032,plain,
    ( v1_funct_1(sK7(sK1,sK2))
    | ~ spl9_158 ),
    inference(resolution,[],[f1028,f70])).

fof(f1029,plain,
    ( spl9_158
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f996,f146,f139,f132,f125,f118,f1027])).

fof(f996,plain,
    ( sP0(sK2,sK1,sK7(sK1,sK2))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f995,f133])).

fof(f995,plain,
    ( v2_struct_0(sK2)
    | sP0(sK2,sK1,sK7(sK1,sK2))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f992,f147])).

fof(f992,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | sP0(sK2,sK1,sK7(sK1,sK2))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(resolution,[],[f989,f140])).

fof(f989,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | sP0(X0,sK1,sK7(sK1,X0)) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f987,f126])).

fof(f987,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | sP0(X0,sK1,sK7(sK1,X0)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f791,f119])).

fof(f1021,plain,
    ( spl9_156
    | ~ spl9_152 ),
    inference(avatar_split_clause,[],[f1005,f1001,f1019])).

fof(f1005,plain,
    ( v5_pre_topc(sK7(sK1,sK1),sK1,sK1)
    | ~ spl9_152 ),
    inference(resolution,[],[f1002,f72])).

fof(f1013,plain,
    ( spl9_154
    | ~ spl9_152 ),
    inference(avatar_split_clause,[],[f1006,f1001,f1011])).

fof(f1006,plain,
    ( v1_funct_1(sK7(sK1,sK1))
    | ~ spl9_152 ),
    inference(resolution,[],[f1002,f70])).

fof(f1003,plain,
    ( spl9_152
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f994,f125,f118,f111,f1001])).

fof(f994,plain,
    ( sP0(sK1,sK1,sK7(sK1,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f993,f112])).

fof(f993,plain,
    ( v2_struct_0(sK1)
    | sP0(sK1,sK1,sK7(sK1,sK1))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f991,f126])).

fof(f991,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | sP0(sK1,sK1,sK7(sK1,sK1))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f989,f119])).

fof(f986,plain,
    ( ~ spl9_151
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f961,f947,f235,f225,f984])).

fof(f984,plain,
    ( spl9_151
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_151])])).

fof(f961,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_144 ),
    inference(forward_demodulation,[],[f956,f236])).

fof(f956,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_144 ),
    inference(resolution,[],[f948,f228])).

fof(f969,plain,
    ( ~ spl9_149
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f959,f947,f967])).

fof(f959,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))),sK7(sK2,sK1))
    | ~ spl9_144 ),
    inference(resolution,[],[f948,f94])).

fof(f962,plain,
    ( ~ spl9_147
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f960,f947,f950])).

fof(f950,plain,
    ( spl9_147
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_147])])).

fof(f960,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_144 ),
    inference(resolution,[],[f948,f102])).

fof(f955,plain,
    ( spl9_144
    | spl9_146
    | ~ spl9_126 ),
    inference(avatar_split_clause,[],[f871,f866,f953,f947])).

fof(f953,plain,
    ( spl9_146
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).

fof(f871,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | r2_hidden(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_126 ),
    inference(resolution,[],[f867,f96])).

fof(f942,plain,
    ( ~ spl9_143
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f927,f913,f235,f225,f940])).

fof(f940,plain,
    ( spl9_143
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_143])])).

fof(f927,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_136 ),
    inference(forward_demodulation,[],[f922,f236])).

fof(f922,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_136 ),
    inference(resolution,[],[f914,f228])).

fof(f935,plain,
    ( ~ spl9_141
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f925,f913,f933])).

fof(f925,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))),sK7(sK2,sK2))
    | ~ spl9_136 ),
    inference(resolution,[],[f914,f94])).

fof(f928,plain,
    ( ~ spl9_139
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f926,f913,f916])).

fof(f916,plain,
    ( spl9_139
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).

fof(f926,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl9_136 ),
    inference(resolution,[],[f914,f102])).

fof(f921,plain,
    ( spl9_136
    | spl9_138
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f861,f856,f919,f913])).

fof(f919,plain,
    ( spl9_138
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f861,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | r2_hidden(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl9_124 ),
    inference(resolution,[],[f857,f96])).

fof(f908,plain,
    ( spl9_108
    | spl9_48
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f720,f715,f346,f727])).

fof(f727,plain,
    ( spl9_108
  <=> r2_hidden(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f346,plain,
    ( spl9_48
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f720,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | r2_hidden(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_106 ),
    inference(resolution,[],[f716,f96])).

fof(f907,plain,
    ( ~ spl9_135
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_128 ),
    inference(avatar_split_clause,[],[f892,f876,f235,f225,f905])).

fof(f905,plain,
    ( spl9_135
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f876,plain,
    ( spl9_128
  <=> r2_hidden(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f892,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_128 ),
    inference(forward_demodulation,[],[f887,f236])).

fof(f887,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_128 ),
    inference(resolution,[],[f877,f228])).

fof(f877,plain,
    ( r2_hidden(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl9_128 ),
    inference(avatar_component_clause,[],[f876])).

fof(f900,plain,
    ( ~ spl9_133
    | ~ spl9_128 ),
    inference(avatar_split_clause,[],[f890,f876,f898])).

fof(f898,plain,
    ( spl9_133
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK7(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f890,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))),sK7(sK1,sK1))
    | ~ spl9_128 ),
    inference(resolution,[],[f877,f94])).

fof(f893,plain,
    ( ~ spl9_131
    | ~ spl9_128 ),
    inference(avatar_split_clause,[],[f891,f876,f879])).

fof(f879,plain,
    ( spl9_131
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f891,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl9_128 ),
    inference(resolution,[],[f877,f102])).

fof(f884,plain,
    ( spl9_128
    | spl9_130
    | ~ spl9_104 ),
    inference(avatar_split_clause,[],[f710,f705,f882,f876])).

fof(f882,plain,
    ( spl9_130
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f710,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | r2_hidden(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl9_104 ),
    inference(resolution,[],[f706,f96])).

fof(f868,plain,
    ( spl9_126
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f849,f146,f139,f125,f118,f111,f866])).

fof(f849,plain,
    ( m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f848,f112])).

fof(f848,plain,
    ( v2_struct_0(sK1)
    | m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f846,f126])).

fof(f846,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f692,f119])).

fof(f692,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | m1_subset_1(sK7(sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) )
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f690,f147])).

fof(f690,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK2)
        | m1_subset_1(sK7(sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) )
    | ~ spl9_8 ),
    inference(resolution,[],[f97,f140])).

fof(f858,plain,
    ( spl9_124
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f851,f146,f139,f132,f856])).

fof(f851,plain,
    ( m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f850,f133])).

fof(f850,plain,
    ( v2_struct_0(sK2)
    | m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f847,f147])).

fof(f847,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | m1_subset_1(sK7(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f692,f140])).

fof(f845,plain,
    ( ~ spl9_93
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f681,f649,f235,f225,f619])).

fof(f619,plain,
    ( spl9_93
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f649,plain,
    ( spl9_98
  <=> r2_hidden(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f681,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_98 ),
    inference(forward_demodulation,[],[f676,f236])).

fof(f676,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_98 ),
    inference(resolution,[],[f650,f228])).

fof(f650,plain,
    ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f649])).

fof(f837,plain,
    ( ~ spl9_123
    | ~ spl9_114 ),
    inference(avatar_split_clause,[],[f801,f767,f835])).

fof(f835,plain,
    ( spl9_123
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK7(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f801,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK7(sK1,sK2)))
    | ~ spl9_114 ),
    inference(resolution,[],[f768,f94])).

fof(f768,plain,
    ( r2_hidden(sK6(sK7(sK1,sK2)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_114 ),
    inference(avatar_component_clause,[],[f767])).

fof(f824,plain,
    ( spl9_120
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f815,f773,f235,f225,f822])).

fof(f822,plain,
    ( spl9_120
  <=> o_0_0_xboole_0 = sK7(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f815,plain,
    ( o_0_0_xboole_0 = sK7(sK1,sK2)
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_116 ),
    inference(forward_demodulation,[],[f811,f236])).

fof(f811,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK7(sK1,sK2)
    | ~ spl9_30
    | ~ spl9_116 ),
    inference(resolution,[],[f774,f229])).

fof(f774,plain,
    ( v1_xboole_0(sK7(sK1,sK2))
    | ~ spl9_116 ),
    inference(avatar_component_clause,[],[f773])).

fof(f810,plain,
    ( spl9_118
    | ~ spl9_114 ),
    inference(avatar_split_clause,[],[f800,f767,f808])).

fof(f808,plain,
    ( spl9_118
  <=> m1_subset_1(sK6(sK7(sK1,sK2)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).

fof(f800,plain,
    ( m1_subset_1(sK6(sK7(sK1,sK2)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_114 ),
    inference(resolution,[],[f768,f95])).

fof(f787,plain,
    ( ~ spl9_81
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f680,f649,f547])).

fof(f680,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_98 ),
    inference(resolution,[],[f650,f102])).

fof(f786,plain,
    ( ~ spl9_30
    | ~ spl9_32
    | spl9_83
    | ~ spl9_100 ),
    inference(avatar_contradiction_clause,[],[f785])).

fof(f785,plain,
    ( $false
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_83
    | ~ spl9_100 ),
    inference(subsumption_resolution,[],[f780,f554])).

fof(f780,plain,
    ( v1_xboole_0(sK3)
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_100 ),
    inference(resolution,[],[f668,f296])).

fof(f668,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_100 ),
    inference(avatar_component_clause,[],[f667])).

fof(f667,plain,
    ( spl9_100
  <=> m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f777,plain,
    ( ~ spl9_80
    | ~ spl9_98 ),
    inference(avatar_contradiction_clause,[],[f776])).

fof(f776,plain,
    ( $false
    | ~ spl9_80
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f551,f680])).

fof(f551,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f550])).

fof(f775,plain,
    ( spl9_114
    | spl9_116
    | spl9_81
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f721,f715,f547,f773,f767])).

fof(f721,plain,
    ( v1_xboole_0(sK7(sK1,sK2))
    | r2_hidden(sK6(sK7(sK1,sK2)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_81
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f719,f548])).

fof(f762,plain,
    ( ~ spl9_113
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f753,f727,f760])).

fof(f760,plain,
    ( spl9_113
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))),sK7(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).

fof(f753,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))),sK7(sK1,sK2))
    | ~ spl9_108 ),
    inference(resolution,[],[f728,f94])).

fof(f728,plain,
    ( r2_hidden(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_108 ),
    inference(avatar_component_clause,[],[f727])).

fof(f743,plain,
    ( spl9_110
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f734,f346,f235,f225,f741])).

fof(f741,plain,
    ( spl9_110
  <=> k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f734,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_48 ),
    inference(forward_demodulation,[],[f730,f236])).

fof(f730,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_48 ),
    inference(resolution,[],[f347,f229])).

fof(f347,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f346])).

fof(f729,plain,
    ( spl9_108
    | spl9_49
    | ~ spl9_106 ),
    inference(avatar_split_clause,[],[f722,f715,f343,f727])).

fof(f343,plain,
    ( spl9_49
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f722,plain,
    ( r2_hidden(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_49
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f720,f344])).

fof(f344,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f343])).

fof(f717,plain,
    ( spl9_106
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f700,f146,f139,f132,f125,f118,f715])).

fof(f700,plain,
    ( m1_subset_1(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f699,f133])).

fof(f699,plain,
    ( v2_struct_0(sK2)
    | m1_subset_1(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f696,f147])).

fof(f696,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | m1_subset_1(sK7(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(resolution,[],[f691,f140])).

fof(f691,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | m1_subset_1(sK7(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f689,f126])).

fof(f689,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK1)
        | m1_subset_1(sK7(sK1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) )
    | ~ spl9_2 ),
    inference(resolution,[],[f97,f119])).

fof(f707,plain,
    ( spl9_104
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f698,f125,f118,f111,f705])).

fof(f698,plain,
    ( m1_subset_1(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f697,f112])).

fof(f697,plain,
    ( v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f695,f126])).

fof(f695,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(sK7(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f691,f119])).

fof(f694,plain,
    ( spl9_98
    | spl9_80
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f643,f634,f550,f649])).

fof(f634,plain,
    ( spl9_94
  <=> m1_subset_1(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f643,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_94 ),
    inference(resolution,[],[f635,f96])).

fof(f635,plain,
    ( m1_subset_1(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f634])).

fof(f693,plain,
    ( spl9_78
    | spl9_80
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f614,f570,f550,f544])).

fof(f544,plain,
    ( spl9_78
  <=> r2_hidden(sK6(sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f570,plain,
    ( spl9_84
  <=> m1_subset_1(sK6(sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f614,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK6(sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_84 ),
    inference(resolution,[],[f571,f96])).

fof(f571,plain,
    ( m1_subset_1(sK6(sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f570])).

fof(f688,plain,
    ( ~ spl9_103
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f679,f649,f686])).

fof(f686,plain,
    ( spl9_103
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK6(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f679,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK6(k1_zfmisc_1(sK3))))
    | ~ spl9_98 ),
    inference(resolution,[],[f650,f94])).

fof(f669,plain,
    ( spl9_100
    | ~ spl9_22
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f654,f584,f189,f667])).

fof(f584,plain,
    ( spl9_86
  <=> k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f654,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_22
    | ~ spl9_86 ),
    inference(superposition,[],[f190,f585])).

fof(f585,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = o_0_0_xboole_0
    | ~ spl9_86 ),
    inference(avatar_component_clause,[],[f584])).

fof(f651,plain,
    ( spl9_98
    | spl9_81
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f644,f634,f547,f649])).

fof(f644,plain,
    ( r2_hidden(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_81
    | ~ spl9_94 ),
    inference(subsumption_resolution,[],[f643,f548])).

fof(f642,plain,
    ( spl9_94
    | spl9_96
    | ~ spl9_22
    | spl9_83 ),
    inference(avatar_split_clause,[],[f629,f553,f189,f640,f634])).

fof(f629,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK3)))
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_22
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f626,f554])).

fof(f626,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(sK3)))
    | v1_xboole_0(sK3)
    | m1_subset_1(sK6(sK6(k1_zfmisc_1(sK3))),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_22 ),
    inference(resolution,[],[f316,f190])).

fof(f622,plain,
    ( spl9_60
    | spl9_56
    | ~ spl9_30
    | ~ spl9_32
    | spl9_37 ),
    inference(avatar_split_clause,[],[f331,f256,f235,f225,f377,f400])).

fof(f400,plain,
    ( spl9_60
  <=> v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f377,plain,
    ( spl9_56
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f256,plain,
    ( spl9_37
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f331,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f325,f257])).

fof(f257,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f256])).

fof(f325,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_30
    | ~ spl9_32 ),
    inference(resolution,[],[f317,f296])).

fof(f317,plain,(
    ! [X3] :
      ( m1_subset_1(sK6(sK6(k1_zfmisc_1(X3))),X3)
      | v1_xboole_0(sK6(k1_zfmisc_1(X3)))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f308,f95])).

fof(f621,plain,
    ( ~ spl9_93
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f606,f544,f235,f225,f619])).

fof(f606,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_78 ),
    inference(forward_demodulation,[],[f601,f236])).

fof(f601,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_78 ),
    inference(resolution,[],[f545,f228])).

fof(f545,plain,
    ( r2_hidden(sK6(sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f544])).

fof(f613,plain,
    ( ~ spl9_91
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f562,f544,f611])).

fof(f611,plain,
    ( spl9_91
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f562,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)),sK6(sK3))
    | ~ spl9_78 ),
    inference(resolution,[],[f545,f94])).

fof(f600,plain,
    ( spl9_88
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f591,f556,f235,f225,f598])).

fof(f598,plain,
    ( spl9_88
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f556,plain,
    ( spl9_82
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f591,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_82 ),
    inference(forward_demodulation,[],[f587,f236])).

fof(f587,plain,
    ( sK3 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_82 ),
    inference(resolution,[],[f557,f229])).

fof(f557,plain,
    ( v1_xboole_0(sK3)
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f556])).

fof(f586,plain,
    ( spl9_86
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f577,f550,f235,f225,f584])).

fof(f577,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_80 ),
    inference(forward_demodulation,[],[f573,f236])).

fof(f573,plain,
    ( k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_80 ),
    inference(resolution,[],[f551,f229])).

fof(f572,plain,
    ( spl9_84
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f561,f544,f570])).

fof(f561,plain,
    ( m1_subset_1(sK6(sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_78 ),
    inference(resolution,[],[f545,f95])).

fof(f565,plain,
    ( ~ spl9_81
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f563,f544,f547])).

fof(f563,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_78 ),
    inference(resolution,[],[f545,f102])).

fof(f558,plain,
    ( spl9_78
    | spl9_80
    | spl9_82
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f310,f189,f556,f550,f544])).

fof(f310,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | r2_hidden(sK6(sK3),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl9_22 ),
    inference(resolution,[],[f291,f190])).

fof(f539,plain,
    ( ~ spl9_77
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f509,f470,f235,f225,f537])).

fof(f537,plain,
    ( spl9_77
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f470,plain,
    ( spl9_68
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f509,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f504,f236])).

fof(f504,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_68 ),
    inference(resolution,[],[f471,f228])).

fof(f471,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f470])).

fof(f532,plain,
    ( ~ spl9_75
    | ~ spl9_58
    | spl9_65 ),
    inference(avatar_split_clause,[],[f525,f434,f391,f530])).

fof(f530,plain,
    ( spl9_75
  <=> o_0_0_xboole_0 != sK6(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f391,plain,
    ( spl9_58
  <=> o_0_0_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f434,plain,
    ( spl9_65
  <=> o_0_0_xboole_0 != sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f525,plain,
    ( o_0_0_xboole_0 != sK6(o_0_0_xboole_0)
    | ~ spl9_58
    | ~ spl9_65 ),
    inference(superposition,[],[f435,f392])).

fof(f392,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f391])).

fof(f435,plain,
    ( o_0_0_xboole_0 != sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_65 ),
    inference(avatar_component_clause,[],[f434])).

fof(f510,plain,
    ( ~ spl9_71
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f508,f470,f473])).

fof(f473,plain,
    ( spl9_71
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f508,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_68 ),
    inference(resolution,[],[f471,f102])).

fof(f498,plain,
    ( spl9_72
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f489,f437,f496])).

fof(f496,plain,
    ( spl9_72
  <=> m1_subset_1(o_0_0_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f437,plain,
    ( spl9_64
  <=> o_0_0_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f489,plain,
    ( m1_subset_1(o_0_0_xboole_0,sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_64 ),
    inference(superposition,[],[f93,f438])).

fof(f438,plain,
    ( o_0_0_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f437])).

fof(f478,plain,
    ( spl9_68
    | spl9_70
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f444,f421,f476,f470])).

fof(f476,plain,
    ( spl9_70
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f421,plain,
    ( spl9_62
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f444,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_62 ),
    inference(resolution,[],[f422,f96])).

fof(f422,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f421])).

fof(f465,plain,
    ( ~ spl9_67
    | ~ spl9_58
    | spl9_61 ),
    inference(avatar_split_clause,[],[f458,f397,f391,f463])).

fof(f463,plain,
    ( spl9_67
  <=> ~ v1_xboole_0(sK6(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f397,plain,
    ( spl9_61
  <=> ~ v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f458,plain,
    ( ~ v1_xboole_0(sK6(o_0_0_xboole_0))
    | ~ spl9_58
    | ~ spl9_61 ),
    inference(superposition,[],[f398,f392])).

fof(f398,plain,
    ( ~ v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f397])).

fof(f439,plain,
    ( spl9_64
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f428,f400,f235,f225,f437])).

fof(f428,plain,
    ( o_0_0_xboole_0 = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_60 ),
    inference(forward_demodulation,[],[f424,f236])).

fof(f424,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_60 ),
    inference(resolution,[],[f401,f229])).

fof(f401,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f400])).

fof(f423,plain,
    ( spl9_62
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f410,f391,f421])).

fof(f410,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_58 ),
    inference(superposition,[],[f93,f392])).

fof(f402,plain,
    ( spl9_60
    | ~ spl9_54 ),
    inference(avatar_split_clause,[],[f394,f371,f400])).

fof(f371,plain,
    ( spl9_54
  <=> ! [X0] : ~ r2_hidden(X0,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f394,plain,
    ( v1_xboole_0(sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_54 ),
    inference(resolution,[],[f372,f213])).

fof(f372,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f371])).

fof(f393,plain,
    ( spl9_58
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f384,f377,f235,f225,f391])).

fof(f384,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_56 ),
    inference(forward_demodulation,[],[f380,f236])).

fof(f380,plain,
    ( sK6(k1_zfmisc_1(o_0_0_xboole_0)) = sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_30
    | ~ spl9_56 ),
    inference(resolution,[],[f378,f229])).

fof(f378,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f377])).

fof(f379,plain,
    ( spl9_54
    | spl9_56
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f313,f160,f377,f371])).

fof(f313,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
        | ~ r2_hidden(X0,sK6(sK6(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))) )
    | ~ spl9_14 ),
    inference(resolution,[],[f292,f93])).

fof(f369,plain,
    ( ~ spl9_53
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f354,f340,f235,f225,f367])).

fof(f367,plain,
    ( spl9_53
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f340,plain,
    ( spl9_46
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f354,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f349,f236])).

fof(f349,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_46 ),
    inference(resolution,[],[f341,f228])).

fof(f341,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f340])).

fof(f362,plain,
    ( ~ spl9_51
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f352,f340,f360])).

fof(f360,plain,
    ( spl9_51
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f352,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))),sK3)
    | ~ spl9_46 ),
    inference(resolution,[],[f341,f94])).

fof(f355,plain,
    ( ~ spl9_49
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f353,f340,f343])).

fof(f353,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_46 ),
    inference(resolution,[],[f341,f102])).

fof(f348,plain,
    ( spl9_46
    | spl9_48
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f214,f189,f346,f340])).

fof(f214,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl9_22 ),
    inference(resolution,[],[f96,f190])).

fof(f307,plain,
    ( ~ spl9_45
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f297,f265,f235,f225,f305])).

fof(f305,plain,
    ( spl9_45
  <=> ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f265,plain,
    ( spl9_38
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f297,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_38 ),
    inference(forward_demodulation,[],[f295,f236])).

fof(f295,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(o_0_0_xboole_0),k1_zfmisc_1(sK6(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl9_30
    | ~ spl9_38 ),
    inference(resolution,[],[f228,f266])).

fof(f266,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f265])).

fof(f285,plain,
    ( spl9_42
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f272,f259,f235,f225,f283])).

fof(f283,plain,
    ( spl9_42
  <=> k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f259,plain,
    ( spl9_36
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f272,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl9_30
    | ~ spl9_32
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f268,f236])).

fof(f268,plain,
    ( k1_zfmisc_1(o_0_0_xboole_0) = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30
    | ~ spl9_36 ),
    inference(resolution,[],[f260,f229])).

fof(f260,plain,
    ( v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f259])).

fof(f278,plain,
    ( spl9_24
    | spl9_40 ),
    inference(avatar_split_clause,[],[f84,f276,f193])).

fof(f84,plain,(
    ! [X4] :
      ( r1_tmap_1(sK1,sK2,sK3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | sP0(sK2,sK1,sK3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( ( ~ r1_tmap_1(sK1,sK2,sK3,sK4)
        & m1_subset_1(sK4,u1_struct_0(sK1)) )
      | ~ sP0(sK2,sK1,sK3) )
    & ( ! [X4] :
          ( r1_tmap_1(sK1,sK2,sK3,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
      | sP0(sK2,sK1,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f54,f58,f57,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X0,X1,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ sP0(X1,X0,X2) )
                & ( ! [X4] :
                      ( r1_tmap_1(X0,X1,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | sP0(X1,X0,X2) )
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
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(sK1,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(sK1)) )
                | ~ sP0(X1,sK1,X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(sK1,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
                | sP0(X1,sK1,X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ sP0(X1,X0,X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(X0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | sP0(X1,X0,X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(X0,sK2,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ sP0(sK2,X0,X2) )
            & ( ! [X4] :
                  ( r1_tmap_1(X0,sK2,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | sP0(sK2,X0,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK2)
        & v2_pre_topc(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(X0,X1,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ sP0(X1,X0,X2) )
          & ( ! [X4] :
                ( r1_tmap_1(X0,X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | sP0(X1,X0,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ~ r1_tmap_1(X0,X1,sK3,X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ sP0(X1,X0,sK3) )
        & ( ! [X4] :
              ( r1_tmap_1(X0,X1,sK3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | sP0(X1,X0,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X0,X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_tmap_1(X0,X1,X2,sK4)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ sP0(X1,X0,X2) )
              & ( ! [X4] :
                    ( r1_tmap_1(X0,X1,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | sP0(X1,X0,X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ sP0(X1,X0,X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | sP0(X1,X0,X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X0,X1,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ sP0(X1,X0,X2) )
              & ( ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | sP0(X1,X0,X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( sP0(X1,X0,X2)
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f32,f47])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <~> ! [X3] :
                    ( r1_tmap_1(X0,X1,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
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
               => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v5_pre_topc(X2,X0,X1)
                    & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X2) )
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
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
             => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => r1_tmap_1(X0,X1,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t55_tmap_1)).

fof(f267,plain,
    ( spl9_36
    | spl9_38
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f241,f235,f265,f259])).

fof(f241,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_32 ),
    inference(superposition,[],[f213,f236])).

fof(f250,plain,
    ( spl9_34
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f242,f235,f248])).

fof(f248,plain,
    ( spl9_34
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f242,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_32 ),
    inference(superposition,[],[f93,f236])).

fof(f237,plain,
    ( spl9_32
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f230,f225,f235])).

fof(f230,plain,
    ( o_0_0_xboole_0 = sK6(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl9_30 ),
    inference(resolution,[],[f226,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f89,f88])).

fof(f88,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',d2_xboole_0)).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',t6_boole)).

fof(f227,plain,
    ( spl9_30
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f220,f160,f225])).

fof(f220,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_14 ),
    inference(resolution,[],[f219,f213])).

fof(f219,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl9_14 ),
    inference(resolution,[],[f218,f93])).

fof(f211,plain,
    ( ~ spl9_25
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f86,f209,f196])).

fof(f86,plain,
    ( ~ r1_tmap_1(sK1,sK2,sK3,sK4)
    | ~ sP0(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f204,plain,
    ( ~ spl9_25
    | spl9_26 ),
    inference(avatar_split_clause,[],[f85,f202,f196])).

fof(f85,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ sP0(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f191,plain,(
    spl9_22 ),
    inference(avatar_split_clause,[],[f83,f189])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f183,plain,(
    spl9_20 ),
    inference(avatar_split_clause,[],[f82,f181])).

fof(f82,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f176,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f88,f174])).

fof(f174,plain,
    ( spl9_18
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f169,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f105,f167])).

fof(f167,plain,
    ( spl9_16
  <=> l1_pre_topc(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f105,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    l1_pre_topc(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f16,f68])).

fof(f68,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK8) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',existence_l1_pre_topc)).

fof(f162,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f87,f160])).

fof(f87,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t55_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f155,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f81,f153])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f148,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f80,f146])).

fof(f80,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f141,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f79,f139])).

fof(f79,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f134,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f78,f132])).

fof(f78,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f127,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f77,f125])).

fof(f77,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f76,f118])).

fof(f76,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f113,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f75,f111])).

fof(f75,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
