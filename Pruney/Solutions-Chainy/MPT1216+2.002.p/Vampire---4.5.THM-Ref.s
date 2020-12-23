%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:44 EST 2020

% Result     : Theorem 3.44s
% Output     : Refutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :  487 (2182 expanded)
%              Number of leaves         :  133 (1150 expanded)
%              Depth                    :   13
%              Number of atoms          : 2558 (7857 expanded)
%              Number of equality atoms :  389 ( 808 expanded)
%              Maximal formula depth    :   63 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8347,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f188,f193,f198,f203,f208,f213,f218,f261,f266,f355,f360,f365,f370,f380,f381,f386,f447,f453,f459,f590,f595,f600,f727,f737,f738,f743,f754,f882,f887,f892,f964,f979,f998,f1031,f1118,f1128,f1133,f1159,f1160,f1161,f1162,f1203,f1218,f1339,f1340,f1341,f1342,f1541,f1552,f1553,f1563,f1568,f1579,f1590,f1591,f1601,f1632,f1658,f1663,f1669,f1684,f1689,f1695,f1896,f1899,f1910,f1911,f1962,f2022,f2137,f2142,f2523,f2576,f2577,f2578,f2665,f2701,f2973,f4005,f4010,f4035,f4040,f4041,f4051,f4110,f4161,f4706,f4721,f4777,f4869,f4884,f5007,f5027,f6985,f8328,f8335,f8336,f8346])).

fof(f8346,plain,
    ( spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(avatar_split_clause,[],[f8310,f1538,f444,f367,f357,f352,f215,f200,f195,f184])).

fof(f184,plain,
    ( spl8_2
  <=> r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f195,plain,
    ( spl8_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f200,plain,
    ( spl8_5
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f215,plain,
    ( spl8_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f352,plain,
    ( spl8_12
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f357,plain,
    ( spl8_13
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f367,plain,
    ( spl8_15
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f444,plain,
    ( spl8_19
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f1538,plain,
    ( spl8_133
  <=> r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).

fof(f8310,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(unit_resulting_resolution,[],[f217,f369,f359,f354,f202,f197,f446,f1540,f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f1540,plain,
    ( r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_133 ),
    inference(avatar_component_clause,[],[f1538])).

fof(f446,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f444])).

fof(f197,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f195])).

fof(f202,plain,
    ( l3_lattices(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f200])).

fof(f354,plain,
    ( v9_lattices(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f352])).

fof(f359,plain,
    ( v8_lattices(sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f357])).

fof(f369,plain,
    ( v6_lattices(sK0)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f367])).

fof(f217,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f215])).

fof(f8336,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k4_lattices(sK0,sK1,sK2) != k2_lattices(sK0,sK1,sK2)
    | k3_lattices(sK0,k6_lattices(sK0),sK1) != k3_lattices(sK0,sK1,k6_lattices(sK0))
    | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)
    | k7_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0))) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))
    | sK1 != k4_lattices(sK0,sK1,sK1)
    | k4_lattices(sK0,k6_lattices(sK0),sK1) != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
    | k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | sK1 != k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))
    | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)))
    | k3_lattices(sK0,k6_lattices(sK0),sK2) != k3_lattices(sK0,sK2,k6_lattices(sK0))
    | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK2)
    | k6_lattices(sK0) != k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) != k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))
    | k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k6_lattices(sK0) != k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) != k2_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))
    | k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))
    | k7_lattices(sK0,sK1) != k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1))
    | k3_lattices(sK0,sK2,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) != k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))
    | k7_lattices(sK0,k4_lattices(sK0,sK1,sK1)) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))
    | k1_lattices(sK0,sK1,sK1) != k3_lattices(sK0,sK1,sK1)
    | sK1 != k1_lattices(sK0,sK1,sK1)
    | sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))
    | k7_lattices(sK0,k3_lattices(sK0,sK1,sK1)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))
    | k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))) != k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) != k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))
    | k1_lattices(sK0,sK2,sK2) != k3_lattices(sK0,sK2,sK2)
    | k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0))) != k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k5_lattices(sK0)))
    | k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) != k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK2,sK2))
    | sK2 != k4_lattices(sK0,k6_lattices(sK0),sK2)
    | k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
    | k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) != k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))
    | k2_lattices(sK0,k7_lattices(sK0,sK1),sK2) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)
    | k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | sK2 != k1_lattices(sK0,sK2,sK2)
    | sK2 != k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2))
    | k4_lattices(sK0,sK1,sK2) != k4_lattices(sK0,sK2,sK1)
    | k2_lattices(sK0,sK2,sK1) != k4_lattices(sK0,sK2,sK1)
    | k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK2,sK1)) != k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK2),sK1)
    | k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK1,sK2)) != k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),sK2)
    | k2_lattices(sK0,k7_lattices(sK0,sK2),k2_lattices(sK0,sK2,sK2)) != k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK2),sK2)
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k2_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8335,plain,
    ( k1_lattices(sK0,sK2,sK2) != k3_lattices(sK0,sK2,sK2)
    | sK2 != k1_lattices(sK0,sK2,sK2)
    | k7_lattices(sK0,k3_lattices(sK0,sK2,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | k4_lattices(sK0,sK1,sK2) != k4_lattices(sK0,sK2,sK1)
    | k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))
    | k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | k4_lattices(sK0,k6_lattices(sK0),sK1) != k4_lattices(sK0,sK1,k6_lattices(sK0))
    | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)
    | sK2 != k4_lattices(sK0,sK2,sK2)
    | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k4_lattices(sK0,sK2,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))
    | k6_lattices(sK0) != k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2))
    | sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
    | sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1))
    | k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,k6_lattices(sK0))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)))
    | k7_lattices(sK0,sK2) != k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)))
    | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2))
    | k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ r1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k7_lattices(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8328,plain,
    ( spl8_1060
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(avatar_split_clause,[],[f8327,f1538,f444,f357,f352,f215,f200,f195,f8318])).

fof(f8318,plain,
    ( spl8_1060
  <=> sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1060])])).

fof(f8327,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(subsumption_resolution,[],[f8326,f217])).

fof(f8326,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(subsumption_resolution,[],[f8325,f359])).

fof(f8325,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(subsumption_resolution,[],[f8324,f354])).

fof(f8324,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(subsumption_resolution,[],[f8323,f202])).

fof(f8323,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(subsumption_resolution,[],[f8322,f197])).

fof(f8322,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_19
    | ~ spl8_133 ),
    inference(subsumption_resolution,[],[f8314,f446])).

fof(f8314,plain,
    ( sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_133 ),
    inference(resolution,[],[f1540,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f6985,plain,
    ( spl8_857
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_50
    | ~ spl8_84 ),
    inference(avatar_split_clause,[],[f5796,f976,f724,f383,f215,f210,f200,f190,f6982])).

fof(f6982,plain,
    ( spl8_857
  <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_857])])).

fof(f190,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f210,plain,
    ( spl8_7
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f383,plain,
    ( spl8_18
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f724,plain,
    ( spl8_50
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f976,plain,
    ( spl8_84
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f5796,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k5_lattices(sK0)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_50
    | ~ spl8_84 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f726,f978,f160])).

fof(f160,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).

fof(f978,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f976])).

fof(f726,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f724])).

fof(f192,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f190])).

fof(f385,plain,
    ( v11_lattices(sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f383])).

fof(f212,plain,
    ( v10_lattices(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f210])).

fof(f5027,plain,
    ( spl8_617
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3688,f724,f362,f263,f215,f195,f190,f5024])).

fof(f5024,plain,
    ( spl8_617
  <=> k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_617])])).

fof(f263,plain,
    ( spl8_10
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f362,plain,
    ( spl8_14
  <=> v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f3688,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),sK2)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f265,f364,f192,f197,f726,f146])).

fof(f146,plain,(
    ! [X6,X4,X0,X5] :
      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ( k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),sK5(X0))) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK5(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f107,f110,f109,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k2_lattices(X0,sK3(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k2_lattices(X0,sK3(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X0] :
      ( ? [X3] :
          ( k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),sK5(X0))) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK5(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ( ( v7_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_lattices)).

fof(f364,plain,
    ( v7_lattices(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f362])).

fof(f265,plain,
    ( l1_lattices(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f263])).

fof(f5007,plain,
    ( spl8_613
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3692,f724,f362,f263,f215,f195,f190,f5004])).

fof(f5004,plain,
    ( spl8_613
  <=> k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK2,sK1)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_613])])).

fof(f3692,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK2,sK1)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK2),sK1)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f265,f364,f197,f192,f726,f146])).

fof(f4884,plain,
    ( spl8_589
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3719,f724,f444,f383,f215,f210,f200,f190,f4881])).

fof(f4881,plain,
    ( spl8_589
  <=> k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_589])])).

fof(f3719,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f446,f726,f160])).

fof(f4869,plain,
    ( spl8_587
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3726,f724,f444,f383,f215,f210,f200,f195,f4866])).

fof(f4866,plain,
    ( spl8_587
  <=> k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_587])])).

fof(f3726,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f197,f726,f160])).

fof(f4777,plain,
    ( spl8_546
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3749,f724,f383,f215,f210,f200,f190,f4653])).

fof(f4653,plain,
    ( spl8_546
  <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_546])])).

fof(f3749,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f726,f726,f160])).

fof(f4721,plain,
    ( spl8_559
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f3761,f961,f724,f444,f383,f215,f210,f200,f4718])).

fof(f4718,plain,
    ( spl8_559
  <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_559])])).

fof(f961,plain,
    ( spl8_83
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f3761,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)))
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f963,f726,f160])).

fof(f963,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl8_83 ),
    inference(avatar_component_clause,[],[f961])).

fof(f4706,plain,
    ( spl8_556
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f3764,f961,f724,f383,f215,f210,f200,f190,f4703])).

fof(f4703,plain,
    ( spl8_556
  <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_556])])).

fof(f3764,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f963,f726,f160])).

fof(f4161,plain,
    ( spl8_451
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3886,f724,f352,f215,f200,f195,f4158])).

fof(f4158,plain,
    ( spl8_451
  <=> k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_451])])).

fof(f3886,plain,
    ( k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f202,f354,f197,f726,f167])).

fof(f167,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),sK7(X0)))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f114,f116,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),sK7(X0)))
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f114,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f4110,plain,
    ( spl8_441
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3897,f724,f377,f258,f215,f195,f4107])).

fof(f4107,plain,
    ( spl8_441
  <=> k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_441])])).

fof(f258,plain,
    ( spl8_9
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f377,plain,
    ( spl8_17
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f3897,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f726,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f260,plain,
    ( l2_lattices(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f258])).

fof(f379,plain,
    ( v4_lattices(sK0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f377])).

fof(f4051,plain,
    ( spl8_430
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f3914,f961,f724,f367,f263,f215,f4048])).

fof(f4048,plain,
    ( spl8_430
  <=> k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_430])])).

fof(f3914,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f963,f726,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f4041,plain,
    ( spl8_424
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3916,f724,f367,f263,f215,f4017])).

fof(f4017,plain,
    ( spl8_424
  <=> k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_424])])).

fof(f3916,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f726,f726,f175])).

fof(f4040,plain,
    ( spl8_428
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3917,f724,f367,f263,f215,f195,f4037])).

fof(f4037,plain,
    ( spl8_428
  <=> k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_428])])).

fof(f3917,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f726,f175])).

fof(f4035,plain,
    ( spl8_427
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3918,f724,f367,f263,f215,f190,f4032])).

fof(f4032,plain,
    ( spl8_427
  <=> k2_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_427])])).

fof(f3918,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f726,f175])).

fof(f4010,plain,
    ( spl8_422
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f3923,f724,f367,f263,f215,f190,f4007])).

fof(f4007,plain,
    ( spl8_422
  <=> k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_422])])).

fof(f3923,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f726,f175])).

fof(f4005,plain,
    ( spl8_421
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f3924,f961,f724,f367,f263,f215,f3998])).

fof(f3998,plain,
    ( spl8_421
  <=> k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_421])])).

fof(f3924,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_50
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f963,f726,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f2973,plain,
    ( spl8_328
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f2344,f961,f444,f383,f215,f210,f200,f195,f2970])).

fof(f2970,plain,
    ( spl8_328
  <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_328])])).

fof(f2344,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f197,f963,f160])).

fof(f2701,plain,
    ( spl8_276
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f2408,f961,f215,f210,f205,f200,f195,f2698])).

fof(f2698,plain,
    ( spl8_276
  <=> k7_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_276])])).

fof(f205,plain,
    ( spl8_6
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2408,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f963,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).

fof(f207,plain,
    ( v17_lattices(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f205])).

fof(f2665,plain,
    ( spl8_269
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f2416,f961,f215,f210,f205,f200,f195,f2662])).

fof(f2662,plain,
    ( spl8_269
  <=> k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_269])])).

fof(f2416,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f963,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).

fof(f2578,plain,
    ( spl8_252
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f2436,f961,f444,f377,f258,f215,f2572])).

fof(f2572,plain,
    ( spl8_252
  <=> k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_252])])).

fof(f2436,plain,
    ( k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f379,f260,f446,f963,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f2577,plain,
    ( spl8_251
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f2437,f961,f377,f258,f215,f195,f2567])).

fof(f2567,plain,
    ( spl8_251
  <=> k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_251])])).

fof(f2437,plain,
    ( k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f963,f174])).

fof(f2576,plain,
    ( spl8_250
    | ~ spl8_3
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f2438,f961,f377,f258,f215,f190,f2562])).

fof(f2562,plain,
    ( spl8_250
  <=> k3_lattices(sK0,k6_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_250])])).

fof(f2438,plain,
    ( k3_lattices(sK0,k6_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k6_lattices(sK0))
    | ~ spl8_3
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f379,f260,f192,f963,f174])).

fof(f2523,plain,
    ( spl8_241
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_83 ),
    inference(avatar_split_clause,[],[f2453,f961,f367,f263,f215,f195,f2513])).

fof(f2513,plain,
    ( spl8_241
  <=> k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_241])])).

fof(f2453,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_83 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f963,f176])).

fof(f2142,plain,
    ( spl8_206
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f2141,f520,f444,f215,f210,f200,f1928])).

fof(f1928,plain,
    ( spl8_206
  <=> k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_206])])).

fof(f520,plain,
    ( spl8_32
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f2141,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f2140,f217])).

fof(f2140,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f2139,f212])).

fof(f2139,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f2138,f521])).

fof(f521,plain,
    ( v14_lattices(sK0)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f520])).

fof(f2138,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1507,f202])).

fof(f1507,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f446,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_lattices)).

fof(f2137,plain,
    ( spl8_207
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f2136,f520,f444,f215,f210,f200,f1933])).

fof(f1933,plain,
    ( spl8_207
  <=> k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_207])])).

fof(f2136,plain,
    ( k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f2135,f217])).

fof(f2135,plain,
    ( k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f2134,f212])).

fof(f2134,plain,
    ( k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_19
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f2133,f521])).

fof(f2133,plain,
    ( k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f1506,f202])).

fof(f1506,plain,
    ( k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f446,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f2022,plain,
    ( spl8_224
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1367,f444,f362,f263,f215,f190,f2019])).

fof(f2019,plain,
    ( spl8_224
  <=> k2_lattices(sK0,k7_lattices(sK0,sK2),k2_lattices(sK0,sK2,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_224])])).

fof(f1367,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k2_lattices(sK0,sK2,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK2),sK2)
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f265,f364,f192,f192,f446,f146])).

fof(f1962,plain,
    ( spl8_212
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1379,f444,f367,f357,f215,f200,f195,f1959])).

fof(f1959,plain,
    ( spl8_212
  <=> r1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_212])])).

fof(f1379,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k7_lattices(sK0,sK2))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f369,f359,f202,f197,f446,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f1911,plain,
    ( spl8_192
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1390,f444,f383,f215,f210,f200,f190,f1850])).

fof(f1850,plain,
    ( spl8_192
  <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_192])])).

fof(f1390,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f192,f446,f160])).

fof(f1910,plain,
    ( spl8_202
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1391,f444,f383,f215,f210,f200,f195,f190,f1907])).

fof(f1907,plain,
    ( spl8_202
  <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_202])])).

fof(f1391,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f197,f446,f160])).

fof(f1899,plain,
    ( spl8_198
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1394,f444,f383,f215,f210,f200,f190,f1883])).

fof(f1883,plain,
    ( spl8_198
  <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_198])])).

fof(f1394,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f446,f446,f160])).

fof(f1896,plain,
    ( spl8_200
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1397,f444,f383,f215,f210,f200,f190,f1893])).

fof(f1893,plain,
    ( spl8_200
  <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_200])])).

fof(f1397,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK2,sK2))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f192,f446,f160])).

fof(f1695,plain,
    ( spl8_162
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1446,f444,f215,f210,f205,f200,f195,f1692])).

fof(f1692,plain,
    ( spl8_162
  <=> k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_162])])).

fof(f1446,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f165])).

fof(f1689,plain,
    ( spl8_161
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1448,f444,f215,f210,f205,f200,f190,f1686])).

fof(f1686,plain,
    ( spl8_161
  <=> k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f1448,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f446,f165])).

fof(f1684,plain,
    ( spl8_160
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1449,f444,f215,f210,f205,f200,f195,f1681])).

fof(f1681,plain,
    ( spl8_160
  <=> k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_160])])).

fof(f1449,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f165])).

fof(f1669,plain,
    ( spl8_157
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1452,f444,f215,f210,f205,f200,f195,f1666])).

fof(f1666,plain,
    ( spl8_157
  <=> k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).

fof(f1452,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f166])).

fof(f1663,plain,
    ( spl8_156
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1454,f444,f215,f210,f205,f200,f190,f1660])).

fof(f1660,plain,
    ( spl8_156
  <=> k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f1454,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f446,f166])).

fof(f1658,plain,
    ( spl8_155
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1455,f444,f215,f210,f205,f200,f195,f1655])).

fof(f1655,plain,
    ( spl8_155
  <=> k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_155])])).

fof(f1455,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f166])).

fof(f1632,plain,
    ( spl8_150
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1461,f444,f352,f215,f200,f195,f1629])).

fof(f1629,plain,
    ( spl8_150
  <=> sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f1461,plain,
    ( sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f202,f354,f197,f446,f167])).

fof(f1601,plain,
    ( spl8_144
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1468,f444,f377,f258,f215,f195,f1598])).

fof(f1598,plain,
    ( spl8_144
  <=> k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f1468,plain,
    ( k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f446,f173])).

fof(f1591,plain,
    ( spl8_142
    | ~ spl8_3
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1470,f444,f377,f258,f215,f190,f1586])).

fof(f1586,plain,
    ( spl8_142
  <=> k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f1470,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | ~ spl8_3
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f379,f260,f192,f446,f174])).

fof(f1590,plain,
    ( spl8_141
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1471,f444,f377,f258,f215,f195,f1581])).

fof(f1581,plain,
    ( spl8_141
  <=> k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f1471,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f446,f174])).

fof(f1579,plain,
    ( spl8_140
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1476,f444,f367,f263,f215,f190,f1576])).

fof(f1576,plain,
    ( spl8_140
  <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).

fof(f1476,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f446,f175])).

fof(f1568,plain,
    ( spl8_138
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1479,f444,f367,f263,f215,f190,f1565])).

fof(f1565,plain,
    ( spl8_138
  <=> k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f1479,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f446,f175])).

fof(f1563,plain,
    ( spl8_137
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1480,f444,f367,f263,f215,f195,f1560])).

fof(f1560,plain,
    ( spl8_137
  <=> k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f1480,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f446,f175])).

fof(f1553,plain,
    ( spl8_135
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1482,f444,f367,f263,f215,f190,f1548])).

fof(f1548,plain,
    ( spl8_135
  <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).

fof(f1482,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | ~ spl8_3
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f446,f176])).

fof(f1552,plain,
    ( spl8_134
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1483,f444,f367,f263,f215,f195,f1543])).

fof(f1543,plain,
    ( spl8_134
  <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f1483,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f446,f176])).

fof(f1541,plain,
    ( spl8_133
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f1488,f444,f367,f357,f352,f215,f200,f195,f184,f1538])).

fof(f1488,plain,
    ( r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f217,f369,f359,f354,f202,f197,f185,f446,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f185,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f184])).

fof(f1342,plain,
    ( spl8_34
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f1333,f520,f215,f210,f200,f190,f532])).

fof(f532,plain,
    ( spl8_34
  <=> k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f1333,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK2)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f217,f212,f202,f192,f521,f158])).

fof(f1341,plain,
    ( spl8_67
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f1334,f520,f215,f210,f200,f195,f824])).

fof(f824,plain,
    ( spl8_67
  <=> k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f1334,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f217,f212,f202,f197,f521,f158])).

fof(f1340,plain,
    ( spl8_33
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f1335,f520,f215,f210,f200,f190,f524])).

fof(f524,plain,
    ( spl8_33
  <=> sK2 = k4_lattices(sK0,k6_lattices(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f1335,plain,
    ( sK2 = k4_lattices(sK0,k6_lattices(sK0),sK2)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f217,f212,f202,f192,f521,f157])).

fof(f1339,plain,
    ( spl8_66
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f1336,f520,f215,f210,f200,f195,f816])).

fof(f816,plain,
    ( spl8_66
  <=> sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f1336,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f217,f212,f202,f197,f521,f157])).

fof(f1218,plain,
    ( spl8_115
    | ~ spl8_3
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f1193,f377,f258,f215,f190,f1215])).

fof(f1215,plain,
    ( spl8_115
  <=> k1_lattices(sK0,sK2,sK2) = k3_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f1193,plain,
    ( k1_lattices(sK0,sK2,sK2) = k3_lattices(sK0,sK2,sK2)
    | ~ spl8_3
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f217,f260,f192,f192,f379,f173])).

fof(f1203,plain,
    ( spl8_112
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f1196,f377,f258,f215,f195,f1200])).

fof(f1200,plain,
    ( spl8_112
  <=> k1_lattices(sK0,sK1,sK1) = k3_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f1196,plain,
    ( k1_lattices(sK0,sK1,sK1) = k3_lattices(sK0,sK1,sK1)
    | ~ spl8_4
    | spl8_8
    | ~ spl8_9
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f217,f260,f197,f197,f379,f173])).

fof(f1162,plain,
    ( spl8_28
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f1089,f367,f357,f352,f215,f200,f190,f493])).

fof(f493,plain,
    ( spl8_28
  <=> sK2 = k1_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f1089,plain,
    ( sK2 = k1_lattices(sK0,sK2,sK2)
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f192,f369,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(f1161,plain,
    ( spl8_63
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f1090,f367,f357,f352,f215,f200,f195,f793])).

fof(f793,plain,
    ( spl8_63
  <=> sK1 = k1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f1090,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f197,f369,f153])).

fof(f1160,plain,
    ( spl8_29
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f1091,f367,f357,f352,f215,f200,f190,f500])).

fof(f500,plain,
    ( spl8_29
  <=> sK2 = k4_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f1091,plain,
    ( sK2 = k4_lattices(sK0,sK2,sK2)
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f192,f369,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).

fof(f1159,plain,
    ( spl8_64
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f1092,f367,f357,f352,f215,f200,f195,f800])).

fof(f800,plain,
    ( spl8_64
  <=> sK1 = k4_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f1092,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK1)
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f197,f369,f154])).

fof(f1133,plain,
    ( spl8_102
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f1098,f367,f263,f215,f195,f190,f1130])).

fof(f1130,plain,
    ( spl8_102
  <=> k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f1098,plain,
    ( k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f217,f265,f197,f192,f369,f175])).

fof(f1128,plain,
    ( spl8_101
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f1099,f367,f263,f215,f195,f190,f1125])).

fof(f1125,plain,
    ( spl8_101
  <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f1099,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f217,f265,f192,f197,f369,f175])).

fof(f1118,plain,
    ( spl8_99
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f1102,f367,f263,f215,f195,f190,f1114])).

fof(f1114,plain,
    ( spl8_99
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f1102,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_8
    | ~ spl8_10
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f217,f265,f197,f192,f369,f176])).

fof(f1031,plain,
    ( spl8_90
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f1000,f352,f215,f200,f190,f1028])).

fof(f1028,plain,
    ( spl8_90
  <=> sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f1000,plain,
    ( sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2))
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f217,f202,f192,f192,f354,f167])).

fof(f998,plain,
    ( spl8_32
    | ~ spl8_5
    | spl8_8
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f995,f276,f215,f200,f520])).

fof(f276,plain,
    ( spl8_11
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f995,plain,
    ( v14_lattices(sK0)
    | ~ spl8_5
    | spl8_8
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f202,f217,f278,f131])).

fof(f131,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

fof(f278,plain,
    ( v15_lattices(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f276])).

fof(f979,plain,
    ( spl8_84
    | spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f966,f263,f215,f976])).

fof(f966,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f217,f265,f145])).

fof(f145,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f964,plain,
    ( spl8_83
    | spl8_8
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f955,f258,f215,f961])).

fof(f955,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | spl8_8
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f217,f260,f144])).

fof(f144,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f892,plain,
    ( spl8_57
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f891,f215,f210,f205,f200,f195,f761])).

fof(f761,plain,
    ( spl8_57
  <=> k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f891,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f890,f217])).

fof(f890,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f889,f212])).

fof(f889,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f888,f207])).

fof(f888,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f703,f202])).

fof(f703,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f197,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).

fof(f887,plain,
    ( spl8_58
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f886,f215,f210,f205,f200,f195,f766])).

fof(f766,plain,
    ( spl8_58
  <=> k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f886,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f885,f217])).

fof(f885,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f884,f212])).

fof(f884,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f883,f207])).

fof(f883,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f702,f202])).

fof(f702,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f197,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).

fof(f882,plain,
    ( spl8_59
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f881,f215,f210,f205,f200,f195,f771])).

fof(f771,plain,
    ( spl8_59
  <=> sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f881,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f880,f217])).

fof(f880,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f879,f212])).

fof(f879,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f878,f207])).

fof(f878,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f701,f202])).

fof(f701,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_4 ),
    inference(resolution,[],[f197,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f754,plain,
    ( spl8_54
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f667,f215,f210,f205,f200,f195,f745])).

fof(f745,plain,
    ( spl8_54
  <=> k7_lattices(sK0,k3_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f667,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f197,f165])).

fof(f743,plain,
    ( spl8_53
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f670,f215,f210,f205,f200,f195,f190,f740])).

fof(f740,plain,
    ( spl8_53
  <=> k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f670,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f197,f166])).

fof(f738,plain,
    ( spl8_51
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f671,f215,f210,f205,f200,f195,f729])).

fof(f729,plain,
    ( spl8_51
  <=> k7_lattices(sK0,k4_lattices(sK0,sK1,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f671,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f197,f166])).

fof(f737,plain,
    ( spl8_52
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f672,f215,f210,f205,f200,f195,f190,f734])).

fof(f734,plain,
    ( spl8_52
  <=> k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f672,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f197,f166])).

fof(f727,plain,
    ( spl8_50
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8 ),
    inference(avatar_split_clause,[],[f674,f215,f200,f195,f724])).

fof(f674,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f202,f197,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f600,plain,
    ( spl8_22
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f599,f215,f210,f205,f200,f190,f461])).

fof(f461,plain,
    ( spl8_22
  <=> k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f599,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f598,f217])).

fof(f598,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f597,f212])).

fof(f597,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f596,f207])).

fof(f596,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f423,f202])).

fof(f423,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f192,f164])).

fof(f595,plain,
    ( spl8_23
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f594,f215,f210,f205,f200,f190,f466])).

fof(f466,plain,
    ( spl8_23
  <=> k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f594,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f593,f217])).

fof(f593,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f592,f212])).

fof(f592,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f591,f207])).

fof(f591,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f422,f202])).

fof(f422,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f192,f163])).

fof(f590,plain,
    ( spl8_24
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f589,f215,f210,f205,f200,f190,f471])).

fof(f471,plain,
    ( spl8_24
  <=> sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f589,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(subsumption_resolution,[],[f588,f217])).

fof(f588,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f587,f212])).

fof(f587,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f586,f207])).

fof(f586,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f421,f202])).

fof(f421,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(resolution,[],[f192,f162])).

fof(f459,plain,
    ( spl8_21
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f390,f215,f210,f205,f200,f190,f455])).

fof(f455,plain,
    ( spl8_21
  <=> k7_lattices(sK0,k3_lattices(sK0,sK2,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f390,plain,
    ( k7_lattices(sK0,k3_lattices(sK0,sK2,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f192,f165])).

fof(f453,plain,
    ( spl8_20
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f392,f215,f210,f205,f200,f190,f449])).

fof(f449,plain,
    ( spl8_20
  <=> k7_lattices(sK0,k4_lattices(sK0,sK2,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f392,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK2,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f192,f166])).

fof(f447,plain,
    ( spl8_19
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8 ),
    inference(avatar_split_clause,[],[f394,f215,f200,f190,f444])).

fof(f394,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_3
    | ~ spl8_5
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f217,f202,f192,f172])).

fof(f386,plain,
    ( spl8_18
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8 ),
    inference(avatar_split_clause,[],[f297,f215,f205,f200,f383])).

fof(f297,plain,
    ( v11_lattices(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f202,f207,f217,f133])).

fof(f133,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f381,plain,
    ( spl8_11
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8 ),
    inference(avatar_split_clause,[],[f298,f215,f205,f200,f276])).

fof(f298,plain,
    ( v15_lattices(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f202,f207,f217,f134])).

fof(f134,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f380,plain,
    ( spl8_17
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f299,f215,f210,f200,f377])).

fof(f299,plain,
    ( v4_lattices(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f202,f212,f217,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f370,plain,
    ( spl8_15
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f301,f215,f210,f200,f367])).

fof(f301,plain,
    ( v6_lattices(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f202,f212,f217,f138])).

fof(f138,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f365,plain,
    ( spl8_14
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f302,f215,f210,f200,f362])).

fof(f302,plain,
    ( v7_lattices(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f202,f212,f217,f139])).

fof(f139,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f360,plain,
    ( spl8_13
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f303,f215,f210,f200,f357])).

fof(f303,plain,
    ( v8_lattices(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f202,f212,f217,f140])).

fof(f140,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f355,plain,
    ( spl8_12
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(avatar_split_clause,[],[f304,f215,f210,f200,f352])).

fof(f304,plain,
    ( v9_lattices(sK0)
    | ~ spl8_5
    | ~ spl8_7
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f202,f212,f217,f141])).

fof(f141,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f266,plain,
    ( spl8_10
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f219,f200,f263])).

fof(f219,plain,
    ( l1_lattices(sK0)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f202,f127])).

fof(f127,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f261,plain,
    ( spl8_9
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f220,f200,f258])).

fof(f220,plain,
    ( l2_lattices(sK0)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f202,f128])).

fof(f128,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f218,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f119,f215])).

fof(f119,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,
    ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
      | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) )
    & ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
      | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f101,f104,f103,f102])).

fof(f102,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK0,X1,k7_lattices(sK0,X2))
                | k4_lattices(sK0,X1,X2) != k5_lattices(sK0) )
              & ( r3_lattices(sK0,X1,k7_lattices(sK0,X2))
                | k4_lattices(sK0,X1,X2) = k5_lattices(sK0) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_lattices(sK0,X1,k7_lattices(sK0,X2))
              | k4_lattices(sK0,X1,X2) != k5_lattices(sK0) )
            & ( r3_lattices(sK0,X1,k7_lattices(sK0,X2))
              | k4_lattices(sK0,X1,X2) = k5_lattices(sK0) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
            | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2) )
          & ( r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
            | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f104,plain,
    ( ? [X2] :
        ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
          | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2) )
        & ( r3_lattices(sK0,sK1,k7_lattices(sK0,X2))
          | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
        | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) )
      & ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
        | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) != k5_lattices(X0) )
              & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                | k4_lattices(X0,X1,X2) = k5_lattices(X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

fof(f213,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f120,f210])).

fof(f120,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f208,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f121,f205])).

fof(f121,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f203,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f122,f200])).

fof(f122,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f198,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f123,f195])).

fof(f123,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f105])).

fof(f193,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f124,f190])).

fof(f124,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f105])).

fof(f188,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f125,f184,f180])).

fof(f180,plain,
    ( spl8_1
  <=> k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f125,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f105])).

fof(f187,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f126,f184,f180])).

fof(f126,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:28:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (26325)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (26317)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (26309)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (26306)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (26305)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (26308)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (26303)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (26329)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (26304)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (26331)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (26324)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (26330)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (26327)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (26307)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (26312)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (26321)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (26318)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (26319)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (26323)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (26322)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (26311)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (26316)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (26328)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.57  % (26315)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.57  % (26313)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (26314)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (26320)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.57  % (26324)Refutation not found, incomplete strategy% (26324)------------------------------
% 0.22/0.57  % (26324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26324)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26324)Memory used [KB]: 10874
% 0.22/0.57  % (26324)Time elapsed: 0.137 s
% 0.22/0.57  % (26324)------------------------------
% 0.22/0.57  % (26324)------------------------------
% 0.22/0.58  % (26319)Refutation not found, incomplete strategy% (26319)------------------------------
% 0.22/0.58  % (26319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (26319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (26319)Memory used [KB]: 10618
% 0.22/0.58  % (26319)Time elapsed: 0.166 s
% 0.22/0.58  % (26319)------------------------------
% 0.22/0.58  % (26319)------------------------------
% 0.22/0.58  % (26302)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.52/0.59  % (26310)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.60  % (26326)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.98/0.77  % (26336)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.13/0.80  % (26335)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.13/0.82  % (26307)Time limit reached!
% 3.13/0.82  % (26307)------------------------------
% 3.13/0.82  % (26307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (26307)Termination reason: Time limit
% 3.13/0.82  
% 3.13/0.82  % (26307)Memory used [KB]: 7419
% 3.13/0.82  % (26307)Time elapsed: 0.403 s
% 3.13/0.82  % (26307)------------------------------
% 3.13/0.82  % (26307)------------------------------
% 3.44/0.87  % (26327)Refutation found. Thanks to Tanya!
% 3.44/0.87  % SZS status Theorem for theBenchmark
% 3.44/0.87  % SZS output start Proof for theBenchmark
% 3.44/0.87  fof(f8347,plain,(
% 3.44/0.87    $false),
% 3.44/0.87    inference(avatar_sat_refutation,[],[f187,f188,f193,f198,f203,f208,f213,f218,f261,f266,f355,f360,f365,f370,f380,f381,f386,f447,f453,f459,f590,f595,f600,f727,f737,f738,f743,f754,f882,f887,f892,f964,f979,f998,f1031,f1118,f1128,f1133,f1159,f1160,f1161,f1162,f1203,f1218,f1339,f1340,f1341,f1342,f1541,f1552,f1553,f1563,f1568,f1579,f1590,f1591,f1601,f1632,f1658,f1663,f1669,f1684,f1689,f1695,f1896,f1899,f1910,f1911,f1962,f2022,f2137,f2142,f2523,f2576,f2577,f2578,f2665,f2701,f2973,f4005,f4010,f4035,f4040,f4041,f4051,f4110,f4161,f4706,f4721,f4777,f4869,f4884,f5007,f5027,f6985,f8328,f8335,f8336,f8346])).
% 3.44/0.88  fof(f8346,plain,(
% 3.44/0.88    spl8_2 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15 | ~spl8_19 | ~spl8_133),
% 3.44/0.88    inference(avatar_split_clause,[],[f8310,f1538,f444,f367,f357,f352,f215,f200,f195,f184])).
% 3.44/0.88  fof(f184,plain,(
% 3.44/0.88    spl8_2 <=> r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.44/0.88  fof(f195,plain,(
% 3.44/0.88    spl8_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.44/0.88  fof(f200,plain,(
% 3.44/0.88    spl8_5 <=> l3_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.44/0.88  fof(f215,plain,(
% 3.44/0.88    spl8_8 <=> v2_struct_0(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.44/0.88  fof(f352,plain,(
% 3.44/0.88    spl8_12 <=> v9_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 3.44/0.88  fof(f357,plain,(
% 3.44/0.88    spl8_13 <=> v8_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 3.44/0.88  fof(f367,plain,(
% 3.44/0.88    spl8_15 <=> v6_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 3.44/0.88  fof(f444,plain,(
% 3.44/0.88    spl8_19 <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 3.44/0.88  fof(f1538,plain,(
% 3.44/0.88    spl8_133 <=> r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_133])])).
% 3.44/0.88  fof(f8310,plain,(
% 3.44/0.88    r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | (~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15 | ~spl8_19 | ~spl8_133)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f359,f354,f202,f197,f446,f1540,f178])).
% 3.44/0.88  fof(f178,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f118])).
% 3.44/0.88  fof(f118,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(nnf_transformation,[],[f99])).
% 3.44/0.88  fof(f99,plain,(
% 3.44/0.88    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f98])).
% 3.44/0.88  fof(f98,plain,(
% 3.44/0.88    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f15])).
% 3.44/0.88  fof(f15,axiom,(
% 3.44/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 3.44/0.88  fof(f1540,plain,(
% 3.44/0.88    r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl8_133),
% 3.44/0.88    inference(avatar_component_clause,[],[f1538])).
% 3.44/0.88  fof(f446,plain,(
% 3.44/0.88    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~spl8_19),
% 3.44/0.88    inference(avatar_component_clause,[],[f444])).
% 3.44/0.88  fof(f197,plain,(
% 3.44/0.88    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_4),
% 3.44/0.88    inference(avatar_component_clause,[],[f195])).
% 3.44/0.88  fof(f202,plain,(
% 3.44/0.88    l3_lattices(sK0) | ~spl8_5),
% 3.44/0.88    inference(avatar_component_clause,[],[f200])).
% 3.44/0.88  fof(f354,plain,(
% 3.44/0.88    v9_lattices(sK0) | ~spl8_12),
% 3.44/0.88    inference(avatar_component_clause,[],[f352])).
% 3.44/0.88  fof(f359,plain,(
% 3.44/0.88    v8_lattices(sK0) | ~spl8_13),
% 3.44/0.88    inference(avatar_component_clause,[],[f357])).
% 3.44/0.88  fof(f369,plain,(
% 3.44/0.88    v6_lattices(sK0) | ~spl8_15),
% 3.44/0.88    inference(avatar_component_clause,[],[f367])).
% 3.44/0.88  fof(f217,plain,(
% 3.44/0.88    ~v2_struct_0(sK0) | spl8_8),
% 3.44/0.88    inference(avatar_component_clause,[],[f215])).
% 3.44/0.88  fof(f8336,plain,(
% 3.44/0.88    k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) | k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) | k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) | k4_lattices(sK0,sK1,sK2) != k2_lattices(sK0,sK1,sK2) | k3_lattices(sK0,k6_lattices(sK0),sK1) != k3_lattices(sK0,sK1,k6_lattices(sK0)) | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) | k7_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0))) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) | sK1 != k4_lattices(sK0,sK1,sK1) | k4_lattices(sK0,k6_lattices(sK0),sK1) != k4_lattices(sK0,sK1,k6_lattices(sK0)) | sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) | k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2))) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | sK1 != k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) | k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)) | k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))) | k3_lattices(sK0,k6_lattices(sK0),sK2) != k3_lattices(sK0,sK2,k6_lattices(sK0)) | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK2) | k6_lattices(sK0) != k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) | k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) != k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) | k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) | k6_lattices(sK0) != k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) != k2_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) | k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) | k7_lattices(sK0,sK1) != k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)) | k3_lattices(sK0,sK2,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) != k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) | k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) | k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) | k7_lattices(sK0,k4_lattices(sK0,sK1,sK1)) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) | k1_lattices(sK0,sK1,sK1) != k3_lattices(sK0,sK1,sK1) | sK1 != k1_lattices(sK0,sK1,sK1) | sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) | k7_lattices(sK0,k3_lattices(sK0,sK1,sK1)) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) | k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))) != k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) | k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) != k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) | k1_lattices(sK0,sK2,sK2) != k3_lattices(sK0,sK2,sK2) | k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0))) != k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k5_lattices(sK0))) | k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) != k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK2,sK2)) | sK2 != k4_lattices(sK0,k6_lattices(sK0),sK2) | k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2)) | k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) != k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) | k2_lattices(sK0,k7_lattices(sK0,sK1),sK2) != k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) | k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) | sK2 != k1_lattices(sK0,sK2,sK2) | sK2 != k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) | k4_lattices(sK0,sK1,sK2) != k4_lattices(sK0,sK2,sK1) | k2_lattices(sK0,sK2,sK1) != k4_lattices(sK0,sK2,sK1) | k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK2,sK1)) != k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK2),sK1) | k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK1,sK2)) != k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),sK2) | k2_lattices(sK0,k7_lattices(sK0,sK2),k2_lattices(sK0,sK2,sK2)) != k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK2),sK2) | k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k2_lattices(sK0,k7_lattices(sK0,sK2),sK2) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)),
% 3.44/0.88    introduced(theory_tautology_sat_conflict,[])).
% 3.44/0.88  fof(f8335,plain,(
% 3.44/0.88    k1_lattices(sK0,sK2,sK2) != k3_lattices(sK0,sK2,sK2) | sK2 != k1_lattices(sK0,sK2,sK2) | k7_lattices(sK0,k3_lattices(sK0,sK2,sK2)) != k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) | k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) != k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) | k4_lattices(sK0,sK1,sK2) != k4_lattices(sK0,sK2,sK1) | k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) | k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2))) | k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | k4_lattices(sK0,k6_lattices(sK0),sK1) != k4_lattices(sK0,sK1,k6_lattices(sK0)) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2) | sK2 != k4_lattices(sK0,sK2,sK2) | sK2 != k7_lattices(sK0,k7_lattices(sK0,sK2)) | k7_lattices(sK0,k4_lattices(sK0,sK2,sK2)) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) | k6_lattices(sK0) != k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)) | sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) | sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) | k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,k6_lattices(sK0))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))) | k7_lattices(sK0,sK2) != k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))) | k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) != k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)) | k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | sK1 != k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))) | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~r1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(theory_tautology_sat_conflict,[])).
% 3.44/0.88  fof(f8328,plain,(
% 3.44/0.88    spl8_1060 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_133),
% 3.44/0.88    inference(avatar_split_clause,[],[f8327,f1538,f444,f357,f352,f215,f200,f195,f8318])).
% 3.44/0.88  fof(f8318,plain,(
% 3.44/0.88    spl8_1060 <=> sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_1060])])).
% 3.44/0.88  fof(f8327,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | (~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_133)),
% 3.44/0.88    inference(subsumption_resolution,[],[f8326,f217])).
% 3.44/0.88  fof(f8326,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_13 | ~spl8_19 | ~spl8_133)),
% 3.44/0.88    inference(subsumption_resolution,[],[f8325,f359])).
% 3.44/0.88  fof(f8325,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_12 | ~spl8_19 | ~spl8_133)),
% 3.44/0.88    inference(subsumption_resolution,[],[f8324,f354])).
% 3.44/0.88  fof(f8324,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_19 | ~spl8_133)),
% 3.44/0.88    inference(subsumption_resolution,[],[f8323,f202])).
% 3.44/0.88  fof(f8323,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_19 | ~spl8_133)),
% 3.44/0.88    inference(subsumption_resolution,[],[f8322,f197])).
% 3.44/0.88  fof(f8322,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl8_19 | ~spl8_133)),
% 3.44/0.88    inference(subsumption_resolution,[],[f8314,f446])).
% 3.44/0.88  fof(f8314,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | ~spl8_133),
% 3.44/0.88    inference(resolution,[],[f1540,f151])).
% 3.44/0.88  fof(f151,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f112])).
% 3.44/0.88  fof(f112,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(nnf_transformation,[],[f56])).
% 3.44/0.88  fof(f56,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f55])).
% 3.44/0.88  fof(f55,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f18])).
% 3.44/0.88  fof(f18,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 3.44/0.88  fof(f6985,plain,(
% 3.44/0.88    spl8_857 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_50 | ~spl8_84),
% 3.44/0.88    inference(avatar_split_clause,[],[f5796,f976,f724,f383,f215,f210,f200,f190,f6982])).
% 3.44/0.88  fof(f6982,plain,(
% 3.44/0.88    spl8_857 <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k5_lattices(sK0)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_857])])).
% 3.44/0.88  fof(f190,plain,(
% 3.44/0.88    spl8_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.44/0.88  fof(f210,plain,(
% 3.44/0.88    spl8_7 <=> v10_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 3.44/0.88  fof(f383,plain,(
% 3.44/0.88    spl8_18 <=> v11_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 3.44/0.88  fof(f724,plain,(
% 3.44/0.88    spl8_50 <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 3.44/0.88  fof(f976,plain,(
% 3.44/0.88    spl8_84 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).
% 3.44/0.88  fof(f5796,plain,(
% 3.44/0.88    k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k5_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k5_lattices(sK0))) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_50 | ~spl8_84)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f726,f978,f160])).
% 3.44/0.88  fof(f160,plain,(
% 3.44/0.88    ( ! [X2,X0,X3,X1] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f72])).
% 3.44/0.88  fof(f72,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f71])).
% 3.44/0.88  fof(f71,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f22])).
% 3.44/0.88  fof(f22,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).
% 3.44/0.88  fof(f978,plain,(
% 3.44/0.88    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl8_84),
% 3.44/0.88    inference(avatar_component_clause,[],[f976])).
% 3.44/0.88  fof(f726,plain,(
% 3.44/0.88    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~spl8_50),
% 3.44/0.88    inference(avatar_component_clause,[],[f724])).
% 3.44/0.88  fof(f192,plain,(
% 3.44/0.88    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl8_3),
% 3.44/0.88    inference(avatar_component_clause,[],[f190])).
% 3.44/0.88  fof(f385,plain,(
% 3.44/0.88    v11_lattices(sK0) | ~spl8_18),
% 3.44/0.88    inference(avatar_component_clause,[],[f383])).
% 3.44/0.88  fof(f212,plain,(
% 3.44/0.88    v10_lattices(sK0) | ~spl8_7),
% 3.44/0.88    inference(avatar_component_clause,[],[f210])).
% 3.44/0.88  fof(f5027,plain,(
% 3.44/0.88    spl8_617 | ~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_14 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3688,f724,f362,f263,f215,f195,f190,f5024])).
% 3.44/0.88  fof(f5024,plain,(
% 3.44/0.88    spl8_617 <=> k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),sK2)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_617])])).
% 3.44/0.88  fof(f263,plain,(
% 3.44/0.88    spl8_10 <=> l1_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 3.44/0.88  fof(f362,plain,(
% 3.44/0.88    spl8_14 <=> v7_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 3.44/0.88  fof(f3688,plain,(
% 3.44/0.88    k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),sK2) | (~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_14 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f265,f364,f192,f197,f726,f146])).
% 3.44/0.88  fof(f146,plain,(
% 3.44/0.88    ( ! [X6,X4,X0,X5] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v7_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f111])).
% 3.44/0.88  fof(f111,plain,(
% 3.44/0.88    ! [X0] : (((v7_lattices(X0) | (((k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),sK5(X0))) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f107,f110,f109,f108])).
% 3.44/0.88  fof(f108,plain,(
% 3.44/0.88    ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k2_lattices(X0,sK3(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 3.44/0.88    introduced(choice_axiom,[])).
% 3.44/0.88  fof(f109,plain,(
% 3.44/0.88    ! [X0] : (? [X2] : (? [X3] : (k2_lattices(X0,sK3(X0),k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 3.44/0.88    introduced(choice_axiom,[])).
% 3.44/0.88  fof(f110,plain,(
% 3.44/0.88    ! [X0] : (? [X3] : (k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),X3)) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),X3) & m1_subset_1(X3,u1_struct_0(X0))) => (k2_lattices(X0,sK3(X0),k2_lattices(X0,sK4(X0),sK5(X0))) != k2_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK5(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 3.44/0.88    introduced(choice_axiom,[])).
% 3.44/0.88  fof(f107,plain,(
% 3.44/0.88    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (! [X6] : (k2_lattices(X0,X4,k2_lattices(X0,X5,X6)) = k2_lattices(X0,k2_lattices(X0,X4,X5),X6) | ~m1_subset_1(X6,u1_struct_0(X0))) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(rectify,[],[f106])).
% 3.44/0.88  fof(f106,plain,(
% 3.44/0.88    ! [X0] : (((v7_lattices(X0) | ? [X1] : (? [X2] : (? [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) != k2_lattices(X0,k2_lattices(X0,X1,X2),X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v7_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(nnf_transformation,[],[f54])).
% 3.44/0.88  fof(f54,plain,(
% 3.44/0.88    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f53])).
% 3.44/0.88  fof(f53,plain,(
% 3.44/0.88    ! [X0] : ((v7_lattices(X0) <=> ! [X1] : (! [X2] : (! [X3] : (k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f7])).
% 3.44/0.88  fof(f7,axiom,(
% 3.44/0.88    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k2_lattices(X0,X1,k2_lattices(X0,X2,X3)) = k2_lattices(X0,k2_lattices(X0,X1,X2),X3))))))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_lattices)).
% 3.44/0.88  fof(f364,plain,(
% 3.44/0.88    v7_lattices(sK0) | ~spl8_14),
% 3.44/0.88    inference(avatar_component_clause,[],[f362])).
% 3.44/0.88  fof(f265,plain,(
% 3.44/0.88    l1_lattices(sK0) | ~spl8_10),
% 3.44/0.88    inference(avatar_component_clause,[],[f263])).
% 3.44/0.88  fof(f5007,plain,(
% 3.44/0.88    spl8_613 | ~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_14 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3692,f724,f362,f263,f215,f195,f190,f5004])).
% 3.44/0.88  fof(f5004,plain,(
% 3.44/0.88    spl8_613 <=> k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK2,sK1)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK2),sK1)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_613])])).
% 3.44/0.88  fof(f3692,plain,(
% 3.44/0.88    k2_lattices(sK0,k7_lattices(sK0,sK1),k2_lattices(sK0,sK2,sK1)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK2),sK1) | (~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_14 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f265,f364,f197,f192,f726,f146])).
% 3.44/0.88  fof(f4884,plain,(
% 3.44/0.88    spl8_589 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3719,f724,f444,f383,f215,f210,f200,f190,f4881])).
% 3.44/0.88  fof(f4881,plain,(
% 3.44/0.88    spl8_589 <=> k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK1),sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_589])])).
% 3.44/0.88  fof(f3719,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f446,f726,f160])).
% 3.44/0.88  fof(f4869,plain,(
% 3.44/0.88    spl8_587 | ~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3726,f724,f444,f383,f215,f210,f200,f195,f4866])).
% 3.44/0.88  fof(f4866,plain,(
% 3.44/0.88    spl8_587 <=> k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_587])])).
% 3.44/0.88  fof(f3726,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) | (~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f197,f726,f160])).
% 3.44/0.88  fof(f4777,plain,(
% 3.44/0.88    spl8_546 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3749,f724,f383,f215,f210,f200,f190,f4653])).
% 3.44/0.88  fof(f4653,plain,(
% 3.44/0.88    spl8_546 <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_546])])).
% 3.44/0.88  fof(f3749,plain,(
% 3.44/0.88    k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f726,f726,f160])).
% 3.44/0.88  fof(f4721,plain,(
% 3.44/0.88    spl8_559 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_50 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f3761,f961,f724,f444,f383,f215,f210,f200,f4718])).
% 3.44/0.88  fof(f4718,plain,(
% 3.44/0.88    spl8_559 <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_559])])).
% 3.44/0.88  fof(f961,plain,(
% 3.44/0.88    spl8_83 <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).
% 3.44/0.88  fof(f3761,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))) | (~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_50 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f963,f726,f160])).
% 3.44/0.88  fof(f963,plain,(
% 3.44/0.88    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | ~spl8_83),
% 3.44/0.88    inference(avatar_component_clause,[],[f961])).
% 3.44/0.88  fof(f4706,plain,(
% 3.44/0.88    spl8_556 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_50 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f3764,f961,f724,f383,f215,f210,f200,f190,f4703])).
% 3.44/0.88  fof(f4703,plain,(
% 3.44/0.88    spl8_556 <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_556])])).
% 3.44/0.88  fof(f3764,plain,(
% 3.44/0.88    k3_lattices(sK0,sK2,k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))) = k4_lattices(sK0,k3_lattices(sK0,sK2,k6_lattices(sK0)),k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_50 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f963,f726,f160])).
% 3.44/0.88  fof(f4161,plain,(
% 3.44/0.88    spl8_451 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3886,f724,f352,f215,f200,f195,f4158])).
% 3.44/0.88  fof(f4158,plain,(
% 3.44/0.88    spl8_451 <=> k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_451])])).
% 3.44/0.88  fof(f3886,plain,(
% 3.44/0.88    k7_lattices(sK0,sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)) | (~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f202,f354,f197,f726,f167])).
% 3.44/0.88  fof(f167,plain,(
% 3.44/0.88    ( ! [X4,X0,X3] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f117])).
% 3.44/0.88  fof(f117,plain,(
% 3.44/0.88    ! [X0] : (((v9_lattices(X0) | ((sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),sK7(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f114,f116,f115])).
% 3.44/0.88  fof(f115,plain,(
% 3.44/0.88    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 3.44/0.88    introduced(choice_axiom,[])).
% 3.44/0.88  fof(f116,plain,(
% 3.44/0.88    ! [X0] : (? [X2] : (sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK6(X0) != k2_lattices(X0,sK6(X0),k1_lattices(X0,sK6(X0),sK7(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 3.44/0.88    introduced(choice_axiom,[])).
% 3.44/0.88  fof(f114,plain,(
% 3.44/0.88    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(rectify,[],[f113])).
% 3.44/0.88  fof(f113,plain,(
% 3.44/0.88    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(nnf_transformation,[],[f86])).
% 3.44/0.88  fof(f86,plain,(
% 3.44/0.88    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f85])).
% 3.44/0.88  fof(f85,plain,(
% 3.44/0.88    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f8])).
% 3.44/0.88  fof(f8,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 3.44/0.88  fof(f4110,plain,(
% 3.44/0.88    spl8_441 | ~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3897,f724,f377,f258,f215,f195,f4107])).
% 3.44/0.88  fof(f4107,plain,(
% 3.44/0.88    spl8_441 <=> k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_441])])).
% 3.44/0.88  fof(f258,plain,(
% 3.44/0.88    spl8_9 <=> l2_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 3.44/0.88  fof(f377,plain,(
% 3.44/0.88    spl8_17 <=> v4_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 3.44/0.88  fof(f3897,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) | (~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f726,f173])).
% 3.44/0.88  fof(f173,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f91])).
% 3.44/0.88  fof(f91,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f90])).
% 3.44/0.88  fof(f90,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f13])).
% 3.44/0.88  fof(f13,axiom,(
% 3.44/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 3.44/0.88  fof(f260,plain,(
% 3.44/0.88    l2_lattices(sK0) | ~spl8_9),
% 3.44/0.88    inference(avatar_component_clause,[],[f258])).
% 3.44/0.88  fof(f379,plain,(
% 3.44/0.88    v4_lattices(sK0) | ~spl8_17),
% 3.44/0.88    inference(avatar_component_clause,[],[f377])).
% 3.44/0.88  fof(f4051,plain,(
% 3.44/0.88    spl8_430 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f3914,f961,f724,f367,f263,f215,f4048])).
% 3.44/0.88  fof(f4048,plain,(
% 3.44/0.88    spl8_430 <=> k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_430])])).
% 3.44/0.88  fof(f3914,plain,(
% 3.44/0.88    k2_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) | (spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f265,f963,f726,f175])).
% 3.44/0.88  fof(f175,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f95])).
% 3.44/0.88  fof(f95,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f94])).
% 3.44/0.88  fof(f94,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f14])).
% 3.44/0.88  fof(f14,axiom,(
% 3.44/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 3.44/0.88  fof(f4041,plain,(
% 3.44/0.88    spl8_424 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3916,f724,f367,f263,f215,f4017])).
% 3.44/0.88  fof(f4017,plain,(
% 3.44/0.88    spl8_424 <=> k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_424])])).
% 3.44/0.88  fof(f3916,plain,(
% 3.44/0.88    k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) | (spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f265,f726,f726,f175])).
% 3.44/0.88  fof(f4040,plain,(
% 3.44/0.88    spl8_428 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3917,f724,f367,f263,f215,f195,f4037])).
% 3.44/0.88  fof(f4037,plain,(
% 3.44/0.88    spl8_428 <=> k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_428])])).
% 3.44/0.88  fof(f3917,plain,(
% 3.44/0.88    k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) | (~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f726,f175])).
% 3.44/0.88  fof(f4035,plain,(
% 3.44/0.88    spl8_427 | ~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3918,f724,f367,f263,f215,f190,f4032])).
% 3.44/0.88  fof(f4032,plain,(
% 3.44/0.88    spl8_427 <=> k2_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_427])])).
% 3.44/0.88  fof(f3918,plain,(
% 3.44/0.88    k2_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) | (~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f726,f175])).
% 3.44/0.88  fof(f4010,plain,(
% 3.44/0.88    spl8_422 | ~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50),
% 3.44/0.88    inference(avatar_split_clause,[],[f3923,f724,f367,f263,f215,f190,f4007])).
% 3.44/0.88  fof(f4007,plain,(
% 3.44/0.88    spl8_422 <=> k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_422])])).
% 3.44/0.88  fof(f3923,plain,(
% 3.44/0.88    k2_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) | (~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f726,f175])).
% 3.44/0.88  fof(f4005,plain,(
% 3.44/0.88    spl8_421 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f3924,f961,f724,f367,f263,f215,f3998])).
% 3.44/0.88  fof(f3998,plain,(
% 3.44/0.88    spl8_421 <=> k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_421])])).
% 3.44/0.88  fof(f3924,plain,(
% 3.44/0.88    k4_lattices(sK0,k7_lattices(sK0,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) | (spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_50 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f265,f963,f726,f176])).
% 3.44/0.88  fof(f176,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f97])).
% 3.44/0.88  fof(f97,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f96])).
% 3.44/0.88  fof(f96,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f6])).
% 3.44/0.88  fof(f6,axiom,(
% 3.44/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 3.44/0.88  fof(f2973,plain,(
% 3.44/0.88    spl8_328 | ~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f2344,f961,f444,f383,f215,f210,f200,f195,f2970])).
% 3.44/0.88  fof(f2970,plain,(
% 3.44/0.88    spl8_328 <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_328])])).
% 3.44/0.88  fof(f2344,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))) | (~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f197,f963,f160])).
% 3.44/0.88  fof(f2701,plain,(
% 3.44/0.88    spl8_276 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f2408,f961,f215,f210,f205,f200,f195,f2698])).
% 3.44/0.88  fof(f2698,plain,(
% 3.44/0.88    spl8_276 <=> k7_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_276])])).
% 3.44/0.88  fof(f205,plain,(
% 3.44/0.88    spl8_6 <=> v17_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.44/0.88  fof(f2408,plain,(
% 3.44/0.88    k7_lattices(sK0,k3_lattices(sK0,sK1,k6_lattices(sK0))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f963,f165])).
% 3.44/0.88  fof(f165,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f82])).
% 3.44/0.88  fof(f82,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f81])).
% 3.44/0.88  fof(f81,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f32])).
% 3.44/0.88  fof(f32,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).
% 3.44/0.88  fof(f207,plain,(
% 3.44/0.88    v17_lattices(sK0) | ~spl8_6),
% 3.44/0.88    inference(avatar_component_clause,[],[f205])).
% 3.44/0.88  fof(f2665,plain,(
% 3.44/0.88    spl8_269 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f2416,f961,f215,f210,f205,f200,f195,f2662])).
% 3.44/0.88  fof(f2662,plain,(
% 3.44/0.88    spl8_269 <=> k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_269])])).
% 3.44/0.88  fof(f2416,plain,(
% 3.44/0.88    k7_lattices(sK0,k4_lattices(sK0,sK1,k6_lattices(sK0))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k6_lattices(sK0))) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f963,f166])).
% 3.44/0.88  fof(f166,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f84])).
% 3.44/0.88  fof(f84,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f83])).
% 3.44/0.88  fof(f83,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f31])).
% 3.44/0.88  fof(f31,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).
% 3.44/0.88  fof(f2578,plain,(
% 3.44/0.88    spl8_252 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f2436,f961,f444,f377,f258,f215,f2572])).
% 3.44/0.88  fof(f2572,plain,(
% 3.44/0.88    spl8_252 <=> k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_252])])).
% 3.44/0.88  fof(f2436,plain,(
% 3.44/0.88    k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k6_lattices(sK0)) | (spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f379,f260,f446,f963,f174])).
% 3.44/0.88  fof(f174,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f93])).
% 3.44/0.88  fof(f93,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f92])).
% 3.44/0.88  fof(f92,plain,(
% 3.44/0.88    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f5])).
% 3.44/0.88  fof(f5,axiom,(
% 3.44/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 3.44/0.88  fof(f2577,plain,(
% 3.44/0.88    spl8_251 | ~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f2437,f961,f377,f258,f215,f195,f2567])).
% 3.44/0.88  fof(f2567,plain,(
% 3.44/0.88    spl8_251 <=> k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_251])])).
% 3.44/0.88  fof(f2437,plain,(
% 3.44/0.88    k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0)) | (~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f963,f174])).
% 3.44/0.88  fof(f2576,plain,(
% 3.44/0.88    spl8_250 | ~spl8_3 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f2438,f961,f377,f258,f215,f190,f2562])).
% 3.44/0.88  fof(f2562,plain,(
% 3.44/0.88    spl8_250 <=> k3_lattices(sK0,k6_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k6_lattices(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_250])])).
% 3.44/0.88  fof(f2438,plain,(
% 3.44/0.88    k3_lattices(sK0,k6_lattices(sK0),sK2) = k3_lattices(sK0,sK2,k6_lattices(sK0)) | (~spl8_3 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f379,f260,f192,f963,f174])).
% 3.44/0.88  fof(f2523,plain,(
% 3.44/0.88    spl8_241 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_83),
% 3.44/0.88    inference(avatar_split_clause,[],[f2453,f961,f367,f263,f215,f195,f2513])).
% 3.44/0.88  fof(f2513,plain,(
% 3.44/0.88    spl8_241 <=> k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_241])])).
% 3.44/0.88  fof(f2453,plain,(
% 3.44/0.88    k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0)) | (~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_83)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f963,f176])).
% 3.44/0.88  fof(f2142,plain,(
% 3.44/0.88    spl8_206 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_19 | ~spl8_32),
% 3.44/0.88    inference(avatar_split_clause,[],[f2141,f520,f444,f215,f210,f200,f1928])).
% 3.44/0.88  fof(f1928,plain,(
% 3.44/0.88    spl8_206 <=> k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_206])])).
% 3.44/0.88  fof(f520,plain,(
% 3.44/0.88    spl8_32 <=> v14_lattices(sK0)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 3.44/0.88  fof(f2141,plain,(
% 3.44/0.88    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | (~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_19 | ~spl8_32)),
% 3.44/0.88    inference(subsumption_resolution,[],[f2140,f217])).
% 3.44/0.88  fof(f2140,plain,(
% 3.44/0.88    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_7 | ~spl8_19 | ~spl8_32)),
% 3.44/0.88    inference(subsumption_resolution,[],[f2139,f212])).
% 3.44/0.88  fof(f2139,plain,(
% 3.44/0.88    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_19 | ~spl8_32)),
% 3.44/0.88    inference(subsumption_resolution,[],[f2138,f521])).
% 3.44/0.88  fof(f521,plain,(
% 3.44/0.88    v14_lattices(sK0) | ~spl8_32),
% 3.44/0.88    inference(avatar_component_clause,[],[f520])).
% 3.44/0.88  fof(f2138,plain,(
% 3.44/0.88    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_19)),
% 3.44/0.88    inference(subsumption_resolution,[],[f1507,f202])).
% 3.44/0.88  fof(f1507,plain,(
% 3.44/0.88    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | ~l3_lattices(sK0) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_19),
% 3.44/0.88    inference(resolution,[],[f446,f158])).
% 3.44/0.88  fof(f158,plain,(
% 3.44/0.88    ( ! [X0,X1] : (k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f68])).
% 3.44/0.88  fof(f68,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f67])).
% 3.44/0.88  fof(f67,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f27])).
% 3.44/0.88  fof(f27,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1)))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_lattices)).
% 3.44/0.88  fof(f2137,plain,(
% 3.44/0.88    spl8_207 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_19 | ~spl8_32),
% 3.44/0.88    inference(avatar_split_clause,[],[f2136,f520,f444,f215,f210,f200,f1933])).
% 3.44/0.88  fof(f1933,plain,(
% 3.44/0.88    spl8_207 <=> k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_207])])).
% 3.44/0.88  fof(f2136,plain,(
% 3.44/0.88    k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | (~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_19 | ~spl8_32)),
% 3.44/0.88    inference(subsumption_resolution,[],[f2135,f217])).
% 3.44/0.88  fof(f2135,plain,(
% 3.44/0.88    k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_7 | ~spl8_19 | ~spl8_32)),
% 3.44/0.88    inference(subsumption_resolution,[],[f2134,f212])).
% 3.44/0.88  fof(f2134,plain,(
% 3.44/0.88    k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_19 | ~spl8_32)),
% 3.44/0.88    inference(subsumption_resolution,[],[f2133,f521])).
% 3.44/0.88  fof(f2133,plain,(
% 3.44/0.88    k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_5 | ~spl8_19)),
% 3.44/0.88    inference(subsumption_resolution,[],[f1506,f202])).
% 3.44/0.88  fof(f1506,plain,(
% 3.44/0.88    k7_lattices(sK0,sK2) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK2)) | ~l3_lattices(sK0) | ~v14_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_19),
% 3.44/0.88    inference(resolution,[],[f446,f157])).
% 3.44/0.88  fof(f157,plain,(
% 3.44/0.88    ( ! [X0,X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f66])).
% 3.44/0.88  fof(f66,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f65])).
% 3.44/0.88  fof(f65,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (k4_lattices(X0,k6_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v14_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f26])).
% 3.44/0.88  fof(f26,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & v14_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,k6_lattices(X0),X1) = X1))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).
% 3.44/0.88  fof(f2022,plain,(
% 3.44/0.88    spl8_224 | ~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_14 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1367,f444,f362,f263,f215,f190,f2019])).
% 3.44/0.88  fof(f2019,plain,(
% 3.44/0.88    spl8_224 <=> k2_lattices(sK0,k7_lattices(sK0,sK2),k2_lattices(sK0,sK2,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK2),sK2)),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_224])])).
% 3.44/0.88  fof(f1367,plain,(
% 3.44/0.88    k2_lattices(sK0,k7_lattices(sK0,sK2),k2_lattices(sK0,sK2,sK2)) = k2_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK2),sK2) | (~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_14 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f265,f364,f192,f192,f446,f146])).
% 3.44/0.88  fof(f1962,plain,(
% 3.44/0.88    spl8_212 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_13 | ~spl8_15 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1379,f444,f367,f357,f215,f200,f195,f1959])).
% 3.44/0.88  fof(f1959,plain,(
% 3.44/0.88    spl8_212 <=> r1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_212])])).
% 3.44/0.88  fof(f1379,plain,(
% 3.44/0.88    r1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k7_lattices(sK0,sK2)) | (~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_13 | ~spl8_15 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f369,f359,f202,f197,f446,f155])).
% 3.44/0.88  fof(f155,plain,(
% 3.44/0.88    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.88    inference(cnf_transformation,[],[f62])).
% 3.44/0.88  fof(f62,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.88    inference(flattening,[],[f61])).
% 3.44/0.88  fof(f61,plain,(
% 3.44/0.88    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.88    inference(ennf_transformation,[],[f20])).
% 3.44/0.88  fof(f20,axiom,(
% 3.44/0.88    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 3.44/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).
% 3.44/0.88  fof(f1911,plain,(
% 3.44/0.88    spl8_192 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1390,f444,f383,f215,f210,f200,f190,f1850])).
% 3.44/0.88  fof(f1850,plain,(
% 3.44/0.88    spl8_192 <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_192])])).
% 3.44/0.88  fof(f1390,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK2),k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f446,f192,f446,f160])).
% 3.44/0.88  fof(f1910,plain,(
% 3.44/0.88    spl8_202 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1391,f444,f383,f215,f210,f200,f195,f190,f1907])).
% 3.44/0.88  fof(f1907,plain,(
% 3.44/0.88    spl8_202 <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_202])])).
% 3.44/0.88  fof(f1391,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f197,f446,f160])).
% 3.44/0.88  fof(f1899,plain,(
% 3.44/0.88    spl8_198 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1394,f444,f383,f215,f210,f200,f190,f1883])).
% 3.44/0.88  fof(f1883,plain,(
% 3.44/0.88    spl8_198 <=> k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_198])])).
% 3.44/0.88  fof(f1394,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)),k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f446,f446,f160])).
% 3.44/0.88  fof(f1896,plain,(
% 3.44/0.88    spl8_200 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1397,f444,f383,f215,f210,f200,f190,f1893])).
% 3.44/0.88  fof(f1893,plain,(
% 3.44/0.88    spl8_200 <=> k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK2,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_200])])).
% 3.44/0.88  fof(f1397,plain,(
% 3.44/0.88    k3_lattices(sK0,sK2,k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK2,sK2)) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_18 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f385,f202,f192,f192,f446,f160])).
% 3.44/0.88  fof(f1695,plain,(
% 3.44/0.88    spl8_162 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1446,f444,f215,f210,f205,f200,f195,f1692])).
% 3.44/0.88  fof(f1692,plain,(
% 3.44/0.88    spl8_162 <=> k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_162])])).
% 3.44/0.88  fof(f1446,plain,(
% 3.44/0.88    k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f165])).
% 3.44/0.88  fof(f1689,plain,(
% 3.44/0.88    spl8_161 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1448,f444,f215,f210,f205,f200,f190,f1686])).
% 3.44/0.88  fof(f1686,plain,(
% 3.44/0.88    spl8_161 <=> k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).
% 3.44/0.88  fof(f1448,plain,(
% 3.44/0.88    k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2))) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f446,f165])).
% 3.44/0.88  fof(f1684,plain,(
% 3.44/0.88    spl8_160 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1449,f444,f215,f210,f205,f200,f195,f1681])).
% 3.44/0.88  fof(f1681,plain,(
% 3.44/0.88    spl8_160 <=> k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_160])])).
% 3.44/0.88  fof(f1449,plain,(
% 3.44/0.88    k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f165])).
% 3.44/0.88  fof(f1669,plain,(
% 3.44/0.88    spl8_157 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1452,f444,f215,f210,f205,f200,f195,f1666])).
% 3.44/0.88  fof(f1666,plain,(
% 3.44/0.88    spl8_157 <=> k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).
% 3.44/0.88  fof(f1452,plain,(
% 3.44/0.88    k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f166])).
% 3.44/0.88  fof(f1663,plain,(
% 3.44/0.88    spl8_156 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1454,f444,f215,f210,f205,f200,f190,f1660])).
% 3.44/0.88  fof(f1660,plain,(
% 3.44/0.88    spl8_156 <=> k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).
% 3.44/0.88  fof(f1454,plain,(
% 3.44/0.88    k7_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK2))) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f446,f166])).
% 3.44/0.88  fof(f1658,plain,(
% 3.44/0.88    spl8_155 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1455,f444,f215,f210,f205,f200,f195,f1655])).
% 3.44/0.88  fof(f1655,plain,(
% 3.44/0.88    spl8_155 <=> k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_155])])).
% 3.44/0.88  fof(f1455,plain,(
% 3.44/0.88    k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f446,f166])).
% 3.44/0.88  fof(f1632,plain,(
% 3.44/0.88    spl8_150 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1461,f444,f352,f215,f200,f195,f1629])).
% 3.44/0.88  fof(f1629,plain,(
% 3.44/0.88    spl8_150 <=> sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).
% 3.44/0.88  fof(f1461,plain,(
% 3.44/0.88    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))) | (~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f202,f354,f197,f446,f167])).
% 3.44/0.88  fof(f1601,plain,(
% 3.44/0.88    spl8_144 | ~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1468,f444,f377,f258,f215,f195,f1598])).
% 3.44/0.88  fof(f1598,plain,(
% 3.44/0.88    spl8_144 <=> k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).
% 3.44/0.88  fof(f1468,plain,(
% 3.44/0.88    k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | (~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f446,f173])).
% 3.44/0.88  fof(f1591,plain,(
% 3.44/0.88    spl8_142 | ~spl8_3 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19),
% 3.44/0.88    inference(avatar_split_clause,[],[f1470,f444,f377,f258,f215,f190,f1586])).
% 3.44/0.88  fof(f1586,plain,(
% 3.44/0.88    spl8_142 <=> k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK2))),
% 3.44/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).
% 3.44/0.88  fof(f1470,plain,(
% 3.44/0.88    k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK2)) | (~spl8_3 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19)),
% 3.44/0.88    inference(unit_resulting_resolution,[],[f217,f379,f260,f192,f446,f174])).
% 3.44/0.89  fof(f1590,plain,(
% 3.44/0.89    spl8_141 | ~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19),
% 3.44/0.89    inference(avatar_split_clause,[],[f1471,f444,f377,f258,f215,f195,f1581])).
% 3.44/0.89  fof(f1581,plain,(
% 3.44/0.89    spl8_141 <=> k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).
% 3.44/0.89  fof(f1471,plain,(
% 3.44/0.89    k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | (~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17 | ~spl8_19)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f379,f260,f197,f446,f174])).
% 3.44/0.89  fof(f1579,plain,(
% 3.44/0.89    spl8_140 | ~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19),
% 3.44/0.89    inference(avatar_split_clause,[],[f1476,f444,f367,f263,f215,f190,f1576])).
% 3.44/0.89  fof(f1576,plain,(
% 3.44/0.89    spl8_140 <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).
% 3.44/0.89  fof(f1476,plain,(
% 3.44/0.89    k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2) | (~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f446,f175])).
% 3.44/0.89  fof(f1568,plain,(
% 3.44/0.89    spl8_138 | ~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19),
% 3.44/0.89    inference(avatar_split_clause,[],[f1479,f444,f367,f263,f215,f190,f1565])).
% 3.44/0.89  fof(f1565,plain,(
% 3.44/0.89    spl8_138 <=> k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).
% 3.44/0.89  fof(f1479,plain,(
% 3.44/0.89    k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) | (~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f446,f175])).
% 3.44/0.89  fof(f1563,plain,(
% 3.44/0.89    spl8_137 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19),
% 3.44/0.89    inference(avatar_split_clause,[],[f1480,f444,f367,f263,f215,f195,f1560])).
% 3.44/0.89  fof(f1560,plain,(
% 3.44/0.89    spl8_137 <=> k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).
% 3.44/0.89  fof(f1480,plain,(
% 3.44/0.89    k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | (~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f446,f175])).
% 3.44/0.89  fof(f1553,plain,(
% 3.44/0.89    spl8_135 | ~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19),
% 3.44/0.89    inference(avatar_split_clause,[],[f1482,f444,f367,f263,f215,f190,f1548])).
% 3.44/0.89  fof(f1548,plain,(
% 3.44/0.89    spl8_135 <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).
% 3.44/0.89  fof(f1482,plain,(
% 3.44/0.89    k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) | (~spl8_3 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f369,f265,f192,f446,f176])).
% 3.44/0.89  fof(f1552,plain,(
% 3.44/0.89    spl8_134 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19),
% 3.44/0.89    inference(avatar_split_clause,[],[f1483,f444,f367,f263,f215,f195,f1543])).
% 3.44/0.89  fof(f1543,plain,(
% 3.44/0.89    spl8_134 <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).
% 3.44/0.89  fof(f1483,plain,(
% 3.44/0.89    k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | (~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15 | ~spl8_19)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f369,f265,f197,f446,f176])).
% 3.44/0.89  fof(f1541,plain,(
% 3.44/0.89    spl8_133 | ~spl8_2 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15 | ~spl8_19),
% 3.44/0.89    inference(avatar_split_clause,[],[f1488,f444,f367,f357,f352,f215,f200,f195,f184,f1538])).
% 3.44/0.89  fof(f1488,plain,(
% 3.44/0.89    r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | (~spl8_2 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15 | ~spl8_19)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f369,f359,f354,f202,f197,f185,f446,f177])).
% 3.44/0.89  fof(f177,plain,(
% 3.44/0.89    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f118])).
% 3.44/0.89  fof(f185,plain,(
% 3.44/0.89    r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~spl8_2),
% 3.44/0.89    inference(avatar_component_clause,[],[f184])).
% 3.44/0.89  fof(f1342,plain,(
% 3.44/0.89    spl8_34 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32),
% 3.44/0.89    inference(avatar_split_clause,[],[f1333,f520,f215,f210,f200,f190,f532])).
% 3.44/0.89  fof(f532,plain,(
% 3.44/0.89    spl8_34 <=> k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 3.44/0.89  fof(f1333,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK2) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f202,f192,f521,f158])).
% 3.44/0.89  fof(f1341,plain,(
% 3.44/0.89    spl8_67 | ~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32),
% 3.44/0.89    inference(avatar_split_clause,[],[f1334,f520,f215,f210,f200,f195,f824])).
% 3.44/0.89  fof(f824,plain,(
% 3.44/0.89    spl8_67 <=> k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).
% 3.44/0.89  fof(f1334,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1) | (~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f202,f197,f521,f158])).
% 3.44/0.89  fof(f1340,plain,(
% 3.44/0.89    spl8_33 | ~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32),
% 3.44/0.89    inference(avatar_split_clause,[],[f1335,f520,f215,f210,f200,f190,f524])).
% 3.44/0.89  fof(f524,plain,(
% 3.44/0.89    spl8_33 <=> sK2 = k4_lattices(sK0,k6_lattices(sK0),sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 3.44/0.89  fof(f1335,plain,(
% 3.44/0.89    sK2 = k4_lattices(sK0,k6_lattices(sK0),sK2) | (~spl8_3 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f202,f192,f521,f157])).
% 3.44/0.89  fof(f1339,plain,(
% 3.44/0.89    spl8_66 | ~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32),
% 3.44/0.89    inference(avatar_split_clause,[],[f1336,f520,f215,f210,f200,f195,f816])).
% 3.44/0.89  fof(f816,plain,(
% 3.44/0.89    spl8_66 <=> sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 3.44/0.89  fof(f1336,plain,(
% 3.44/0.89    sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1) | (~spl8_4 | ~spl8_5 | ~spl8_7 | spl8_8 | ~spl8_32)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f202,f197,f521,f157])).
% 3.44/0.89  fof(f1218,plain,(
% 3.44/0.89    spl8_115 | ~spl8_3 | spl8_8 | ~spl8_9 | ~spl8_17),
% 3.44/0.89    inference(avatar_split_clause,[],[f1193,f377,f258,f215,f190,f1215])).
% 3.44/0.89  fof(f1215,plain,(
% 3.44/0.89    spl8_115 <=> k1_lattices(sK0,sK2,sK2) = k3_lattices(sK0,sK2,sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).
% 3.44/0.89  fof(f1193,plain,(
% 3.44/0.89    k1_lattices(sK0,sK2,sK2) = k3_lattices(sK0,sK2,sK2) | (~spl8_3 | spl8_8 | ~spl8_9 | ~spl8_17)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f260,f192,f192,f379,f173])).
% 3.44/0.89  fof(f1203,plain,(
% 3.44/0.89    spl8_112 | ~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17),
% 3.44/0.89    inference(avatar_split_clause,[],[f1196,f377,f258,f215,f195,f1200])).
% 3.44/0.89  fof(f1200,plain,(
% 3.44/0.89    spl8_112 <=> k1_lattices(sK0,sK1,sK1) = k3_lattices(sK0,sK1,sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).
% 3.44/0.89  fof(f1196,plain,(
% 3.44/0.89    k1_lattices(sK0,sK1,sK1) = k3_lattices(sK0,sK1,sK1) | (~spl8_4 | spl8_8 | ~spl8_9 | ~spl8_17)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f260,f197,f197,f379,f173])).
% 3.44/0.89  fof(f1162,plain,(
% 3.44/0.89    spl8_28 | ~spl8_3 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15),
% 3.44/0.89    inference(avatar_split_clause,[],[f1089,f367,f357,f352,f215,f200,f190,f493])).
% 3.44/0.89  fof(f493,plain,(
% 3.44/0.89    spl8_28 <=> sK2 = k1_lattices(sK0,sK2,sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 3.44/0.89  fof(f1089,plain,(
% 3.44/0.89    sK2 = k1_lattices(sK0,sK2,sK2) | (~spl8_3 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f192,f369,f153])).
% 3.44/0.89  fof(f153,plain,(
% 3.44/0.89    ( ! [X0,X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f58])).
% 3.44/0.89  fof(f58,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f57])).
% 3.44/0.89  fof(f57,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f16])).
% 3.44/0.89  fof(f16,axiom,(
% 3.44/0.89    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).
% 3.44/0.89  fof(f1161,plain,(
% 3.44/0.89    spl8_63 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15),
% 3.44/0.89    inference(avatar_split_clause,[],[f1090,f367,f357,f352,f215,f200,f195,f793])).
% 3.44/0.89  fof(f793,plain,(
% 3.44/0.89    spl8_63 <=> sK1 = k1_lattices(sK0,sK1,sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).
% 3.44/0.89  fof(f1090,plain,(
% 3.44/0.89    sK1 = k1_lattices(sK0,sK1,sK1) | (~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f197,f369,f153])).
% 3.44/0.89  fof(f1160,plain,(
% 3.44/0.89    spl8_29 | ~spl8_3 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15),
% 3.44/0.89    inference(avatar_split_clause,[],[f1091,f367,f357,f352,f215,f200,f190,f500])).
% 3.44/0.89  fof(f500,plain,(
% 3.44/0.89    spl8_29 <=> sK2 = k4_lattices(sK0,sK2,sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 3.44/0.89  fof(f1091,plain,(
% 3.44/0.89    sK2 = k4_lattices(sK0,sK2,sK2) | (~spl8_3 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f192,f369,f154])).
% 3.44/0.89  fof(f154,plain,(
% 3.44/0.89    ( ! [X0,X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f60])).
% 3.44/0.89  fof(f60,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f59])).
% 3.44/0.89  fof(f59,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k4_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f17])).
% 3.44/0.89  fof(f17,axiom,(
% 3.44/0.89    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattices(X0,X1,X1) = X1))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_lattices)).
% 3.44/0.89  fof(f1159,plain,(
% 3.44/0.89    spl8_64 | ~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15),
% 3.44/0.89    inference(avatar_split_clause,[],[f1092,f367,f357,f352,f215,f200,f195,f800])).
% 3.44/0.89  fof(f800,plain,(
% 3.44/0.89    spl8_64 <=> sK1 = k4_lattices(sK0,sK1,sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 3.44/0.89  fof(f1092,plain,(
% 3.44/0.89    sK1 = k4_lattices(sK0,sK1,sK1) | (~spl8_4 | ~spl8_5 | spl8_8 | ~spl8_12 | ~spl8_13 | ~spl8_15)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f202,f359,f354,f197,f369,f154])).
% 3.44/0.89  fof(f1133,plain,(
% 3.44/0.89    spl8_102 | ~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15),
% 3.44/0.89    inference(avatar_split_clause,[],[f1098,f367,f263,f215,f195,f190,f1130])).
% 3.44/0.89  fof(f1130,plain,(
% 3.44/0.89    spl8_102 <=> k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 3.44/0.89  fof(f1098,plain,(
% 3.44/0.89    k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1) | (~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f265,f197,f192,f369,f175])).
% 3.44/0.89  fof(f1128,plain,(
% 3.44/0.89    spl8_101 | ~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15),
% 3.44/0.89    inference(avatar_split_clause,[],[f1099,f367,f263,f215,f195,f190,f1125])).
% 3.44/0.89  fof(f1125,plain,(
% 3.44/0.89    spl8_101 <=> k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).
% 3.44/0.89  fof(f1099,plain,(
% 3.44/0.89    k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2) | (~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f265,f192,f197,f369,f175])).
% 3.44/0.89  fof(f1118,plain,(
% 3.44/0.89    spl8_99 | ~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15),
% 3.44/0.89    inference(avatar_split_clause,[],[f1102,f367,f263,f215,f195,f190,f1114])).
% 3.44/0.89  fof(f1114,plain,(
% 3.44/0.89    spl8_99 <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).
% 3.44/0.89  fof(f1102,plain,(
% 3.44/0.89    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) | (~spl8_3 | ~spl8_4 | spl8_8 | ~spl8_10 | ~spl8_15)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f265,f197,f192,f369,f176])).
% 3.44/0.89  fof(f1031,plain,(
% 3.44/0.89    spl8_90 | ~spl8_3 | ~spl8_5 | spl8_8 | ~spl8_12),
% 3.44/0.89    inference(avatar_split_clause,[],[f1000,f352,f215,f200,f190,f1028])).
% 3.44/0.89  fof(f1028,plain,(
% 3.44/0.89    spl8_90 <=> sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).
% 3.44/0.89  fof(f1000,plain,(
% 3.44/0.89    sK2 = k2_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) | (~spl8_3 | ~spl8_5 | spl8_8 | ~spl8_12)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f202,f192,f192,f354,f167])).
% 3.44/0.89  fof(f998,plain,(
% 3.44/0.89    spl8_32 | ~spl8_5 | spl8_8 | ~spl8_11),
% 3.44/0.89    inference(avatar_split_clause,[],[f995,f276,f215,f200,f520])).
% 3.44/0.89  fof(f276,plain,(
% 3.44/0.89    spl8_11 <=> v15_lattices(sK0)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 3.44/0.89  fof(f995,plain,(
% 3.44/0.89    v14_lattices(sK0) | (~spl8_5 | spl8_8 | ~spl8_11)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f217,f278,f131])).
% 3.44/0.89  fof(f131,plain,(
% 3.44/0.89    ( ! [X0] : (v14_lattices(X0) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f40])).
% 3.44/0.89  fof(f40,plain,(
% 3.44/0.89    ! [X0] : ((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | ~v15_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.44/0.89    inference(flattening,[],[f39])).
% 3.44/0.89  fof(f39,plain,(
% 3.44/0.89    ! [X0] : (((v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0)) | (~v15_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.44/0.89    inference(ennf_transformation,[],[f3])).
% 3.44/0.89  fof(f3,axiom,(
% 3.44/0.89    ! [X0] : (l3_lattices(X0) => ((v15_lattices(X0) & ~v2_struct_0(X0)) => (v14_lattices(X0) & v13_lattices(X0) & ~v2_struct_0(X0))))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).
% 3.44/0.89  fof(f278,plain,(
% 3.44/0.89    v15_lattices(sK0) | ~spl8_11),
% 3.44/0.89    inference(avatar_component_clause,[],[f276])).
% 3.44/0.89  fof(f979,plain,(
% 3.44/0.89    spl8_84 | spl8_8 | ~spl8_10),
% 3.44/0.89    inference(avatar_split_clause,[],[f966,f263,f215,f976])).
% 3.44/0.89  fof(f966,plain,(
% 3.44/0.89    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl8_8 | ~spl8_10)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f265,f145])).
% 3.44/0.89  fof(f145,plain,(
% 3.44/0.89    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f52])).
% 3.44/0.89  fof(f52,plain,(
% 3.44/0.89    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f51])).
% 3.44/0.89  fof(f51,plain,(
% 3.44/0.89    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f9])).
% 3.44/0.89  fof(f9,axiom,(
% 3.44/0.89    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 3.44/0.89  fof(f964,plain,(
% 3.44/0.89    spl8_83 | spl8_8 | ~spl8_9),
% 3.44/0.89    inference(avatar_split_clause,[],[f955,f258,f215,f961])).
% 3.44/0.89  fof(f955,plain,(
% 3.44/0.89    m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) | (spl8_8 | ~spl8_9)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f260,f144])).
% 3.44/0.89  fof(f144,plain,(
% 3.44/0.89    ( ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f50])).
% 3.44/0.89  fof(f50,plain,(
% 3.44/0.89    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f49])).
% 3.44/0.89  fof(f49,plain,(
% 3.44/0.89    ! [X0] : (m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f10])).
% 3.44/0.89  fof(f10,axiom,(
% 3.44/0.89    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).
% 3.44/0.89  fof(f892,plain,(
% 3.44/0.89    spl8_57 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f891,f215,f210,f205,f200,f195,f761])).
% 3.44/0.89  fof(f761,plain,(
% 3.44/0.89    spl8_57 <=> k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 3.44/0.89  fof(f891,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(subsumption_resolution,[],[f890,f217])).
% 3.44/0.89  fof(f890,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 3.44/0.89    inference(subsumption_resolution,[],[f889,f212])).
% 3.44/0.89  fof(f889,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6)),
% 3.44/0.89    inference(subsumption_resolution,[],[f888,f207])).
% 3.44/0.89  fof(f888,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5)),
% 3.44/0.89    inference(subsumption_resolution,[],[f703,f202])).
% 3.44/0.89  fof(f703,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_4),
% 3.44/0.89    inference(resolution,[],[f197,f164])).
% 3.44/0.89  fof(f164,plain,(
% 3.44/0.89    ( ! [X0,X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f80])).
% 3.44/0.89  fof(f80,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f79])).
% 3.44/0.89  fof(f79,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f28])).
% 3.44/0.89  fof(f28,axiom,(
% 3.44/0.89    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).
% 3.44/0.89  fof(f887,plain,(
% 3.44/0.89    spl8_58 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f886,f215,f210,f205,f200,f195,f766])).
% 3.44/0.89  fof(f766,plain,(
% 3.44/0.89    spl8_58 <=> k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 3.44/0.89  fof(f886,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(subsumption_resolution,[],[f885,f217])).
% 3.44/0.89  fof(f885,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 3.44/0.89    inference(subsumption_resolution,[],[f884,f212])).
% 3.44/0.89  fof(f884,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6)),
% 3.44/0.89    inference(subsumption_resolution,[],[f883,f207])).
% 3.44/0.89  fof(f883,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5)),
% 3.44/0.89    inference(subsumption_resolution,[],[f702,f202])).
% 3.44/0.89  fof(f702,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_4),
% 3.44/0.89    inference(resolution,[],[f197,f163])).
% 3.44/0.89  fof(f163,plain,(
% 3.44/0.89    ( ! [X0,X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f78])).
% 3.44/0.89  fof(f78,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f77])).
% 3.44/0.89  fof(f77,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f29])).
% 3.44/0.89  fof(f29,axiom,(
% 3.44/0.89    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).
% 3.44/0.89  fof(f882,plain,(
% 3.44/0.89    spl8_59 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f881,f215,f210,f205,f200,f195,f771])).
% 3.44/0.89  fof(f771,plain,(
% 3.44/0.89    spl8_59 <=> sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 3.44/0.89  fof(f881,plain,(
% 3.44/0.89    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(subsumption_resolution,[],[f880,f217])).
% 3.44/0.89  fof(f880,plain,(
% 3.44/0.89    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 3.44/0.89    inference(subsumption_resolution,[],[f879,f212])).
% 3.44/0.89  fof(f879,plain,(
% 3.44/0.89    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5 | ~spl8_6)),
% 3.44/0.89    inference(subsumption_resolution,[],[f878,f207])).
% 3.44/0.89  fof(f878,plain,(
% 3.44/0.89    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_4 | ~spl8_5)),
% 3.44/0.89    inference(subsumption_resolution,[],[f701,f202])).
% 3.44/0.89  fof(f701,plain,(
% 3.44/0.89    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_4),
% 3.44/0.89    inference(resolution,[],[f197,f162])).
% 3.44/0.89  fof(f162,plain,(
% 3.44/0.89    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f76])).
% 3.44/0.89  fof(f76,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f75])).
% 3.44/0.89  fof(f75,plain,(
% 3.44/0.89    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f30])).
% 3.44/0.89  fof(f30,axiom,(
% 3.44/0.89    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).
% 3.44/0.89  fof(f754,plain,(
% 3.44/0.89    spl8_54 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f667,f215,f210,f205,f200,f195,f745])).
% 3.44/0.89  fof(f745,plain,(
% 3.44/0.89    spl8_54 <=> k7_lattices(sK0,k3_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 3.44/0.89  fof(f667,plain,(
% 3.44/0.89    k7_lattices(sK0,k3_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f197,f165])).
% 3.44/0.89  fof(f743,plain,(
% 3.44/0.89    spl8_53 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f670,f215,f210,f205,f200,f195,f190,f740])).
% 3.44/0.89  fof(f740,plain,(
% 3.44/0.89    spl8_53 <=> k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 3.44/0.89  fof(f670,plain,(
% 3.44/0.89    k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f197,f166])).
% 3.44/0.89  fof(f738,plain,(
% 3.44/0.89    spl8_51 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f671,f215,f210,f205,f200,f195,f729])).
% 3.44/0.89  fof(f729,plain,(
% 3.44/0.89    spl8_51 <=> k7_lattices(sK0,k4_lattices(sK0,sK1,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 3.44/0.89  fof(f671,plain,(
% 3.44/0.89    k7_lattices(sK0,k4_lattices(sK0,sK1,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK1)) | (~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f197,f197,f166])).
% 3.44/0.89  fof(f737,plain,(
% 3.44/0.89    spl8_52 | ~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f672,f215,f210,f205,f200,f195,f190,f734])).
% 3.44/0.89  fof(f734,plain,(
% 3.44/0.89    spl8_52 <=> k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 3.44/0.89  fof(f672,plain,(
% 3.44/0.89    k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | (~spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f197,f166])).
% 3.44/0.89  fof(f727,plain,(
% 3.44/0.89    spl8_50 | ~spl8_4 | ~spl8_5 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f674,f215,f200,f195,f724])).
% 3.44/0.89  fof(f674,plain,(
% 3.44/0.89    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | (~spl8_4 | ~spl8_5 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f202,f197,f172])).
% 3.44/0.89  fof(f172,plain,(
% 3.44/0.89    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f89])).
% 3.44/0.89  fof(f89,plain,(
% 3.44/0.89    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.44/0.89    inference(flattening,[],[f88])).
% 3.44/0.89  fof(f88,plain,(
% 3.44/0.89    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.44/0.89    inference(ennf_transformation,[],[f11])).
% 3.44/0.89  fof(f11,axiom,(
% 3.44/0.89    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 3.44/0.89  fof(f600,plain,(
% 3.44/0.89    spl8_22 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f599,f215,f210,f205,f200,f190,f461])).
% 3.44/0.89  fof(f461,plain,(
% 3.44/0.89    spl8_22 <=> k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 3.44/0.89  fof(f599,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(subsumption_resolution,[],[f598,f217])).
% 3.44/0.89  fof(f598,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 3.44/0.89    inference(subsumption_resolution,[],[f597,f212])).
% 3.44/0.89  fof(f597,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5 | ~spl8_6)),
% 3.44/0.89    inference(subsumption_resolution,[],[f596,f207])).
% 3.44/0.89  fof(f596,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5)),
% 3.44/0.89    inference(subsumption_resolution,[],[f423,f202])).
% 3.44/0.89  fof(f423,plain,(
% 3.44/0.89    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_3),
% 3.44/0.89    inference(resolution,[],[f192,f164])).
% 3.44/0.89  fof(f595,plain,(
% 3.44/0.89    spl8_23 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f594,f215,f210,f205,f200,f190,f466])).
% 3.44/0.89  fof(f466,plain,(
% 3.44/0.89    spl8_23 <=> k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 3.44/0.89  fof(f594,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(subsumption_resolution,[],[f593,f217])).
% 3.44/0.89  fof(f593,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 3.44/0.89    inference(subsumption_resolution,[],[f592,f212])).
% 3.44/0.89  fof(f592,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5 | ~spl8_6)),
% 3.44/0.89    inference(subsumption_resolution,[],[f591,f207])).
% 3.44/0.89  fof(f591,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5)),
% 3.44/0.89    inference(subsumption_resolution,[],[f422,f202])).
% 3.44/0.89  fof(f422,plain,(
% 3.44/0.89    k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_3),
% 3.44/0.89    inference(resolution,[],[f192,f163])).
% 3.44/0.89  fof(f590,plain,(
% 3.44/0.89    spl8_24 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f589,f215,f210,f205,f200,f190,f471])).
% 3.44/0.89  fof(f471,plain,(
% 3.44/0.89    spl8_24 <=> sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 3.44/0.89  fof(f589,plain,(
% 3.44/0.89    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(subsumption_resolution,[],[f588,f217])).
% 3.44/0.89  fof(f588,plain,(
% 3.44/0.89    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7)),
% 3.44/0.89    inference(subsumption_resolution,[],[f587,f212])).
% 3.44/0.89  fof(f587,plain,(
% 3.44/0.89    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5 | ~spl8_6)),
% 3.44/0.89    inference(subsumption_resolution,[],[f586,f207])).
% 3.44/0.89  fof(f586,plain,(
% 3.44/0.89    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl8_3 | ~spl8_5)),
% 3.44/0.89    inference(subsumption_resolution,[],[f421,f202])).
% 3.44/0.89  fof(f421,plain,(
% 3.44/0.89    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl8_3),
% 3.44/0.89    inference(resolution,[],[f192,f162])).
% 3.44/0.89  fof(f459,plain,(
% 3.44/0.89    spl8_21 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f390,f215,f210,f205,f200,f190,f455])).
% 3.44/0.89  fof(f455,plain,(
% 3.44/0.89    spl8_21 <=> k7_lattices(sK0,k3_lattices(sK0,sK2,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 3.44/0.89  fof(f390,plain,(
% 3.44/0.89    k7_lattices(sK0,k3_lattices(sK0,sK2,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f192,f165])).
% 3.44/0.89  fof(f453,plain,(
% 3.44/0.89    spl8_20 | ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f392,f215,f210,f205,f200,f190,f449])).
% 3.44/0.89  fof(f449,plain,(
% 3.44/0.89    spl8_20 <=> k7_lattices(sK0,k4_lattices(sK0,sK2,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2))),
% 3.44/0.89    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 3.44/0.89  fof(f392,plain,(
% 3.44/0.89    k7_lattices(sK0,k4_lattices(sK0,sK2,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK2)) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f212,f207,f202,f192,f192,f166])).
% 3.44/0.89  fof(f447,plain,(
% 3.44/0.89    spl8_19 | ~spl8_3 | ~spl8_5 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f394,f215,f200,f190,f444])).
% 3.44/0.89  fof(f394,plain,(
% 3.44/0.89    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | (~spl8_3 | ~spl8_5 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f217,f202,f192,f172])).
% 3.44/0.89  fof(f386,plain,(
% 3.44/0.89    spl8_18 | ~spl8_5 | ~spl8_6 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f297,f215,f205,f200,f383])).
% 3.44/0.89  fof(f297,plain,(
% 3.44/0.89    v11_lattices(sK0) | (~spl8_5 | ~spl8_6 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f207,f217,f133])).
% 3.44/0.89  fof(f133,plain,(
% 3.44/0.89    ( ! [X0] : (v11_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f42])).
% 3.44/0.89  fof(f42,plain,(
% 3.44/0.89    ! [X0] : ((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.44/0.89    inference(flattening,[],[f41])).
% 3.44/0.89  fof(f41,plain,(
% 3.44/0.89    ! [X0] : (((v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0)) | (~v17_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.44/0.89    inference(ennf_transformation,[],[f35])).
% 3.44/0.89  fof(f35,plain,(
% 3.44/0.89    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 3.44/0.89    inference(pure_predicate_removal,[],[f4])).
% 3.44/0.89  fof(f4,axiom,(
% 3.44/0.89    ! [X0] : (l3_lattices(X0) => ((v17_lattices(X0) & ~v2_struct_0(X0)) => (v16_lattices(X0) & v15_lattices(X0) & v11_lattices(X0) & ~v2_struct_0(X0))))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).
% 3.44/0.89  fof(f381,plain,(
% 3.44/0.89    spl8_11 | ~spl8_5 | ~spl8_6 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f298,f215,f205,f200,f276])).
% 3.44/0.89  fof(f298,plain,(
% 3.44/0.89    v15_lattices(sK0) | (~spl8_5 | ~spl8_6 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f207,f217,f134])).
% 3.44/0.89  fof(f134,plain,(
% 3.44/0.89    ( ! [X0] : (v15_lattices(X0) | ~v17_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f42])).
% 3.44/0.89  fof(f380,plain,(
% 3.44/0.89    spl8_17 | ~spl8_5 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f299,f215,f210,f200,f377])).
% 3.44/0.89  fof(f299,plain,(
% 3.44/0.89    v4_lattices(sK0) | (~spl8_5 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f212,f217,f136])).
% 3.44/0.89  fof(f136,plain,(
% 3.44/0.89    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f44])).
% 3.44/0.89  fof(f44,plain,(
% 3.44/0.89    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.44/0.89    inference(flattening,[],[f43])).
% 3.44/0.89  fof(f43,plain,(
% 3.44/0.89    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.44/0.89    inference(ennf_transformation,[],[f2])).
% 3.44/0.89  fof(f2,axiom,(
% 3.44/0.89    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 3.44/0.89  fof(f370,plain,(
% 3.44/0.89    spl8_15 | ~spl8_5 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f301,f215,f210,f200,f367])).
% 3.44/0.89  fof(f301,plain,(
% 3.44/0.89    v6_lattices(sK0) | (~spl8_5 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f212,f217,f138])).
% 3.44/0.89  fof(f138,plain,(
% 3.44/0.89    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f44])).
% 3.44/0.89  fof(f365,plain,(
% 3.44/0.89    spl8_14 | ~spl8_5 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f302,f215,f210,f200,f362])).
% 3.44/0.89  fof(f302,plain,(
% 3.44/0.89    v7_lattices(sK0) | (~spl8_5 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f212,f217,f139])).
% 3.44/0.89  fof(f139,plain,(
% 3.44/0.89    ( ! [X0] : (v7_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f44])).
% 3.44/0.89  fof(f360,plain,(
% 3.44/0.89    spl8_13 | ~spl8_5 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f303,f215,f210,f200,f357])).
% 3.44/0.89  fof(f303,plain,(
% 3.44/0.89    v8_lattices(sK0) | (~spl8_5 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f212,f217,f140])).
% 3.44/0.89  fof(f140,plain,(
% 3.44/0.89    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f44])).
% 3.44/0.89  fof(f355,plain,(
% 3.44/0.89    spl8_12 | ~spl8_5 | ~spl8_7 | spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f304,f215,f210,f200,f352])).
% 3.44/0.89  fof(f304,plain,(
% 3.44/0.89    v9_lattices(sK0) | (~spl8_5 | ~spl8_7 | spl8_8)),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f212,f217,f141])).
% 3.44/0.89  fof(f141,plain,(
% 3.44/0.89    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f44])).
% 3.44/0.89  fof(f266,plain,(
% 3.44/0.89    spl8_10 | ~spl8_5),
% 3.44/0.89    inference(avatar_split_clause,[],[f219,f200,f263])).
% 3.44/0.89  fof(f219,plain,(
% 3.44/0.89    l1_lattices(sK0) | ~spl8_5),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f127])).
% 3.44/0.89  fof(f127,plain,(
% 3.44/0.89    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f38])).
% 3.44/0.89  fof(f38,plain,(
% 3.44/0.89    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.44/0.89    inference(ennf_transformation,[],[f12])).
% 3.44/0.89  fof(f12,axiom,(
% 3.44/0.89    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.44/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 3.44/0.89  fof(f261,plain,(
% 3.44/0.89    spl8_9 | ~spl8_5),
% 3.44/0.89    inference(avatar_split_clause,[],[f220,f200,f258])).
% 3.44/0.89  fof(f220,plain,(
% 3.44/0.89    l2_lattices(sK0) | ~spl8_5),
% 3.44/0.89    inference(unit_resulting_resolution,[],[f202,f128])).
% 3.44/0.89  fof(f128,plain,(
% 3.44/0.89    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.44/0.89    inference(cnf_transformation,[],[f38])).
% 3.44/0.89  fof(f218,plain,(
% 3.44/0.89    ~spl8_8),
% 3.44/0.89    inference(avatar_split_clause,[],[f119,f215])).
% 3.44/0.89  fof(f119,plain,(
% 3.44/0.89    ~v2_struct_0(sK0)),
% 3.44/0.89    inference(cnf_transformation,[],[f105])).
% 3.44/0.89  fof(f105,plain,(
% 3.44/0.89    (((~r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 3.44/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f101,f104,f103,f102])).
% 3.44/0.89  fof(f102,plain,(
% 3.44/0.89    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) != k5_lattices(sK0)) & (r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) = k5_lattices(sK0)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 3.44/0.89    introduced(choice_axiom,[])).
% 3.44/0.89  fof(f103,plain,(
% 3.44/0.89    ? [X1] : (? [X2] : ((~r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) != k5_lattices(sK0)) & (r3_lattices(sK0,X1,k7_lattices(sK0,X2)) | k4_lattices(sK0,X1,X2) = k5_lattices(sK0)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 3.44/0.89    introduced(choice_axiom,[])).
% 3.44/0.90  fof(f104,plain,(
% 3.44/0.90    ? [X2] : ((~r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,X2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,X2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)) & (r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 3.44/0.90    introduced(choice_axiom,[])).
% 3.44/0.90  fof(f101,plain,(
% 3.44/0.90    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.44/0.90    inference(flattening,[],[f100])).
% 3.44/0.90  fof(f100,plain,(
% 3.44/0.90    ? [X0] : (? [X1] : (? [X2] : (((~r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) = k5_lattices(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.44/0.90    inference(nnf_transformation,[],[f37])).
% 3.44/0.90  fof(f37,plain,(
% 3.44/0.90    ? [X0] : (? [X1] : (? [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <~> r3_lattices(X0,X1,k7_lattices(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.44/0.90    inference(flattening,[],[f36])).
% 3.44/0.90  fof(f36,plain,(
% 3.44/0.90    ? [X0] : (? [X1] : (? [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <~> r3_lattices(X0,X1,k7_lattices(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.44/0.90    inference(ennf_transformation,[],[f34])).
% 3.44/0.90  fof(f34,negated_conjecture,(
% 3.44/0.90    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 3.44/0.90    inference(negated_conjecture,[],[f33])).
% 3.44/0.90  fof(f33,conjecture,(
% 3.44/0.90    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 3.44/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).
% 3.44/0.90  fof(f213,plain,(
% 3.44/0.90    spl8_7),
% 3.44/0.90    inference(avatar_split_clause,[],[f120,f210])).
% 3.44/0.90  fof(f120,plain,(
% 3.44/0.90    v10_lattices(sK0)),
% 3.44/0.90    inference(cnf_transformation,[],[f105])).
% 3.44/0.90  fof(f208,plain,(
% 3.44/0.90    spl8_6),
% 3.44/0.90    inference(avatar_split_clause,[],[f121,f205])).
% 3.44/0.90  fof(f121,plain,(
% 3.44/0.90    v17_lattices(sK0)),
% 3.44/0.90    inference(cnf_transformation,[],[f105])).
% 3.44/0.90  fof(f203,plain,(
% 3.44/0.90    spl8_5),
% 3.44/0.90    inference(avatar_split_clause,[],[f122,f200])).
% 3.44/0.90  fof(f122,plain,(
% 3.44/0.90    l3_lattices(sK0)),
% 3.44/0.90    inference(cnf_transformation,[],[f105])).
% 3.44/0.90  fof(f198,plain,(
% 3.44/0.90    spl8_4),
% 3.44/0.90    inference(avatar_split_clause,[],[f123,f195])).
% 3.44/0.90  fof(f123,plain,(
% 3.44/0.90    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.44/0.90    inference(cnf_transformation,[],[f105])).
% 3.44/0.90  fof(f193,plain,(
% 3.44/0.90    spl8_3),
% 3.44/0.90    inference(avatar_split_clause,[],[f124,f190])).
% 3.44/0.90  fof(f124,plain,(
% 3.44/0.90    m1_subset_1(sK2,u1_struct_0(sK0))),
% 3.44/0.90    inference(cnf_transformation,[],[f105])).
% 3.44/0.90  fof(f188,plain,(
% 3.44/0.90    spl8_1 | spl8_2),
% 3.44/0.90    inference(avatar_split_clause,[],[f125,f184,f180])).
% 3.44/0.90  fof(f180,plain,(
% 3.44/0.90    spl8_1 <=> k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)),
% 3.44/0.90    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.44/0.90  fof(f125,plain,(
% 3.44/0.90    r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,sK2)),
% 3.44/0.90    inference(cnf_transformation,[],[f105])).
% 3.44/0.90  fof(f187,plain,(
% 3.44/0.90    ~spl8_1 | ~spl8_2),
% 3.44/0.90    inference(avatar_split_clause,[],[f126,f184,f180])).
% 3.44/0.90  fof(f126,plain,(
% 3.44/0.90    ~r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | k5_lattices(sK0) != k4_lattices(sK0,sK1,sK2)),
% 3.44/0.90    inference(cnf_transformation,[],[f105])).
% 3.44/0.90  % SZS output end Proof for theBenchmark
% 3.44/0.90  % (26327)------------------------------
% 3.44/0.90  % (26327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.44/0.90  % (26327)Termination reason: Refutation
% 3.44/0.90  
% 3.44/0.90  % (26327)Memory used [KB]: 13688
% 3.44/0.90  % (26327)Time elapsed: 0.448 s
% 3.44/0.90  % (26327)------------------------------
% 3.44/0.90  % (26327)------------------------------
% 3.44/0.90  % (26301)Success in time 0.533 s
%------------------------------------------------------------------------------
