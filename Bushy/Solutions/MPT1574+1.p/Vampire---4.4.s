%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t52_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  513 (2130 expanded)
%              Number of leaves         :  145 ( 774 expanded)
%              Depth                    :   22
%              Number of atoms          : 1665 (6832 expanded)
%              Number of equality atoms :  128 ( 470 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2093,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f88,f95,f120,f127,f168,f183,f194,f204,f244,f252,f267,f283,f292,f299,f330,f343,f350,f368,f390,f397,f428,f452,f464,f471,f500,f530,f539,f546,f581,f606,f629,f649,f656,f681,f690,f696,f703,f719,f735,f742,f787,f805,f834,f843,f862,f904,f927,f941,f948,f977,f1023,f1048,f1057,f1064,f1097,f1121,f1140,f1147,f1167,f1236,f1269,f1277,f1292,f1316,f1345,f1377,f1441,f1497,f1530,f1539,f1552,f1559,f1584,f1610,f1643,f1652,f1671,f1726,f1737,f1754,f1771,f1789,f1800,f1832,f1876,f1911,f1937,f1947,f1969,f1971,f2032,f2064,f2076,f2078,f2080,f2086,f2092])).

fof(f2092,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | spl5_11
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(avatar_contradiction_clause,[],[f2091])).

fof(f2091,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f2090,f80])).

fof(f80,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2090,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f2089,f87])).

fof(f87,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2089,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f2088,f119])).

fof(f119,plain,
    ( r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_8
  <=> r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f2088,plain,
    ( ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f2087,f2082])).

fof(f2082,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(unit_resulting_resolution,[],[f80,f87,f718,f2057,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t5_yellow_0)).

fof(f2057,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_212 ),
    inference(avatar_component_clause,[],[f2056])).

fof(f2056,plain,
    ( spl5_212
  <=> r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).

fof(f718,plain,
    ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl5_82
  <=> m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f2087,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_11
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f2083,f126])).

fof(f126,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_11
  <=> k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f2083,plain,
    ( k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_212 ),
    inference(resolution,[],[f2057,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
              | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK2(X0,X1,X2))
          | r1_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r2_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) )
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t49_yellow_0)).

fof(f2086,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | spl5_11
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(avatar_contradiction_clause,[],[f2085])).

fof(f2085,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f2081,f2082])).

fof(f2081,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_212 ),
    inference(unit_resulting_resolution,[],[f80,f87,f119,f126,f2057,f64])).

fof(f2080,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | spl5_11
    | ~ spl5_82
    | spl5_213 ),
    inference(avatar_contradiction_clause,[],[f2079])).

fof(f2079,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_213 ),
    inference(subsumption_resolution,[],[f2067,f2071])).

fof(f2071,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_82
    | ~ spl5_213 ),
    inference(unit_resulting_resolution,[],[f80,f87,f718,f2054,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2054,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_213 ),
    inference(avatar_component_clause,[],[f2053])).

fof(f2053,plain,
    ( spl5_213
  <=> ~ r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_213])])).

fof(f2067,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_213 ),
    inference(unit_resulting_resolution,[],[f126,f2054,f707])).

fof(f707,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
        | r1_lattice3(sK0,X1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
        | k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f119,f322])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X1)
        | r1_lattice3(sK0,X1,sK2(sK0,X1,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f321,f87])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,sK2(sK0,X1,X0))
        | r1_lattice3(sK0,X1,sK2(sK0,X1,X0))
        | ~ r2_yellow_0(sK0,X1)
        | ~ l1_orders_2(sK0)
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f63,f80])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | r1_lattice3(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2078,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | spl5_11
    | ~ spl5_82
    | spl5_213 ),
    inference(avatar_contradiction_clause,[],[f2077])).

fof(f2077,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_213 ),
    inference(subsumption_resolution,[],[f2068,f2071])).

fof(f2068,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_213 ),
    inference(unit_resulting_resolution,[],[f119,f126,f2054,f322])).

fof(f2076,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | spl5_11
    | ~ spl5_82
    | spl5_213 ),
    inference(avatar_contradiction_clause,[],[f2075])).

fof(f2075,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_82
    | ~ spl5_213 ),
    inference(subsumption_resolution,[],[f2070,f2071])).

fof(f2070,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_213 ),
    inference(unit_resulting_resolution,[],[f80,f87,f119,f126,f2054,f63])).

fof(f2064,plain,
    ( spl5_212
    | ~ spl5_215
    | spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | spl5_11 ),
    inference(avatar_split_clause,[],[f1618,f125,f118,f86,f79,f2062,f2056])).

fof(f2062,plain,
    ( spl5_215
  <=> ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_215])])).

fof(f1618,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f1617,f126])).

fof(f1617,plain,
    ( k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(duplicate_literal_removal,[],[f1611])).

fof(f1611,plain,
    ( k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | r1_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f1041,f707])).

fof(f1041,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f1040,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',commutativity_k3_xboole_0)).

fof(f1040,plain,
    ( ! [X0] :
        ( k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | ~ r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f1037,f708])).

fof(f708,plain,
    ( ! [X2] :
        ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X2),u1_struct_0(sK0))
        | k2_yellow_0(sK0,X2) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f119,f236])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ r2_yellow_0(sK0,X0)
        | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f234,f87])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,X0)
        | ~ l1_orders_2(sK0)
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f62,f80])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1037,plain,
    ( ! [X0] :
        ( k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f810,f211])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),X1) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f210,f87])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f61,f80])).

fof(f810,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
        | k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f809,f67])).

fof(f809,plain,
    ( ! [X1] :
        ( k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
        | ~ r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f807,f708])).

fof(f807,plain,
    ( ! [X1] :
        ( k2_yellow_0(sK0,X1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
        | ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f706,f211])).

fof(f706,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | ~ r1_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f119,f414])).

fof(f414,plain,
    ( ! [X2,X3] :
        ( ~ r2_yellow_0(sK0,X2)
        | k2_yellow_0(sK0,X2) = k2_yellow_0(sK0,X3)
        | ~ r1_lattice3(sK0,X2,sK2(sK0,X2,X3))
        | ~ r1_lattice3(sK0,k3_xboole_0(X3,u1_struct_0(sK0)),sK2(sK0,X2,X3)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f413,f236])).

fof(f413,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k3_xboole_0(X3,u1_struct_0(sK0)),sK2(sK0,X2,X3))
        | k2_yellow_0(sK0,X2) = k2_yellow_0(sK0,X3)
        | ~ r1_lattice3(sK0,X2,sK2(sK0,X2,X3))
        | ~ r2_yellow_0(sK0,X2) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f412,f80])).

fof(f412,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k3_xboole_0(X3,u1_struct_0(sK0)),sK2(sK0,X2,X3))
        | k2_yellow_0(sK0,X2) = k2_yellow_0(sK0,X3)
        | ~ r1_lattice3(sK0,X2,sK2(sK0,X2,X3))
        | ~ r2_yellow_0(sK0,X2)
        | v2_struct_0(sK0) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f410,f87])).

fof(f410,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2(sK0,X2,X3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k3_xboole_0(X3,u1_struct_0(sK0)),sK2(sK0,X2,X3))
        | k2_yellow_0(sK0,X2) = k2_yellow_0(sK0,X3)
        | ~ r1_lattice3(sK0,X2,sK2(sK0,X2,X3))
        | ~ r2_yellow_0(sK0,X2)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f211,f64])).

fof(f2032,plain,
    ( ~ spl5_211
    | spl5_203 ),
    inference(avatar_split_clause,[],[f1981,f1900,f2030])).

fof(f2030,plain,
    ( spl5_211
  <=> ~ r2_hidden(sK3(sK3(k1_xboole_0)),sK3(sK3(sK3(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).

fof(f1900,plain,
    ( spl5_203
  <=> ~ v1_xboole_0(sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_203])])).

fof(f1981,plain,
    ( ~ r2_hidden(sK3(sK3(k1_xboole_0)),sK3(sK3(sK3(k1_xboole_0))))
    | ~ spl5_203 ),
    inference(unit_resulting_resolution,[],[f65,f1901,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',antisymmetry_r2_hidden)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t2_subset)).

fof(f1901,plain,
    ( ~ v1_xboole_0(sK3(sK3(k1_xboole_0)))
    | ~ spl5_203 ),
    inference(avatar_component_clause,[],[f1900])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',existence_m1_subset_1)).

fof(f1971,plain,
    ( ~ spl5_148
    | ~ spl5_202
    | spl5_205 ),
    inference(avatar_contradiction_clause,[],[f1970])).

fof(f1970,plain,
    ( $false
    | ~ spl5_148
    | ~ spl5_202
    | ~ spl5_205 ),
    inference(subsumption_resolution,[],[f1964,f65])).

fof(f1964,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl5_148
    | ~ spl5_202
    | ~ spl5_205 ),
    inference(backward_demodulation,[],[f1951,f1910])).

fof(f1910,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK3(sK3(k1_xboole_0)))
    | ~ spl5_205 ),
    inference(avatar_component_clause,[],[f1909])).

fof(f1909,plain,
    ( spl5_205
  <=> ~ m1_subset_1(sK3(k1_xboole_0),sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).

fof(f1951,plain,
    ( k1_xboole_0 = sK3(sK3(k1_xboole_0))
    | ~ spl5_148
    | ~ spl5_202 ),
    inference(unit_resulting_resolution,[],[f1344,f1904,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t8_boole)).

fof(f1904,plain,
    ( v1_xboole_0(sK3(sK3(k1_xboole_0)))
    | ~ spl5_202 ),
    inference(avatar_component_clause,[],[f1903])).

fof(f1903,plain,
    ( spl5_202
  <=> v1_xboole_0(sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f1344,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_148 ),
    inference(avatar_component_clause,[],[f1343])).

fof(f1343,plain,
    ( spl5_148
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f1969,plain,
    ( ~ spl5_148
    | spl5_189
    | ~ spl5_196
    | ~ spl5_202 ),
    inference(avatar_contradiction_clause,[],[f1968])).

fof(f1968,plain,
    ( $false
    | ~ spl5_148
    | ~ spl5_189
    | ~ spl5_196
    | ~ spl5_202 ),
    inference(subsumption_resolution,[],[f1961,f1753])).

fof(f1753,plain,
    ( ~ r2_hidden(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl5_189 ),
    inference(avatar_component_clause,[],[f1752])).

fof(f1752,plain,
    ( spl5_189
  <=> ~ r2_hidden(k1_xboole_0,sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_189])])).

fof(f1961,plain,
    ( r2_hidden(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl5_148
    | ~ spl5_196
    | ~ spl5_202 ),
    inference(backward_demodulation,[],[f1951,f1799])).

fof(f1799,plain,
    ( r2_hidden(sK3(sK3(k1_xboole_0)),sK3(k1_xboole_0))
    | ~ spl5_196 ),
    inference(avatar_component_clause,[],[f1798])).

fof(f1798,plain,
    ( spl5_196
  <=> r2_hidden(sK3(sK3(k1_xboole_0)),sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).

fof(f1947,plain,
    ( spl5_208
    | spl5_203 ),
    inference(avatar_split_clause,[],[f1913,f1900,f1945])).

fof(f1945,plain,
    ( spl5_208
  <=> r2_hidden(sK3(sK3(sK3(k1_xboole_0))),sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f1913,plain,
    ( r2_hidden(sK3(sK3(sK3(k1_xboole_0))),sK3(sK3(k1_xboole_0)))
    | ~ spl5_203 ),
    inference(unit_resulting_resolution,[],[f65,f1901,f71])).

fof(f1937,plain,
    ( ~ spl5_207
    | spl5_203 ),
    inference(avatar_split_clause,[],[f1923,f1900,f1935])).

fof(f1935,plain,
    ( spl5_207
  <=> ~ m1_subset_1(sK3(sK3(k1_xboole_0)),sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f1923,plain,
    ( ~ m1_subset_1(sK3(sK3(k1_xboole_0)),sK3(sK3(k1_xboole_0)))
    | ~ spl5_203 ),
    inference(unit_resulting_resolution,[],[f1901,f132])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f106,f71])).

fof(f1911,plain,
    ( spl5_202
    | ~ spl5_205
    | ~ spl5_196 ),
    inference(avatar_split_clause,[],[f1868,f1798,f1909,f1903])).

fof(f1868,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK3(sK3(k1_xboole_0)))
    | v1_xboole_0(sK3(sK3(k1_xboole_0)))
    | ~ spl5_196 ),
    inference(resolution,[],[f1799,f106])).

fof(f1876,plain,
    ( ~ spl5_201
    | spl5_193 ),
    inference(avatar_split_clause,[],[f1835,f1766,f1874])).

fof(f1874,plain,
    ( spl5_201
  <=> ~ r2_hidden(sK3(k1_xboole_0),sK3(sK3(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_201])])).

fof(f1766,plain,
    ( spl5_193
  <=> ~ v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).

fof(f1835,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0),sK3(sK3(k1_xboole_0)))
    | ~ spl5_193 ),
    inference(unit_resulting_resolution,[],[f65,f1767,f106])).

fof(f1767,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_193 ),
    inference(avatar_component_clause,[],[f1766])).

fof(f1832,plain,
    ( spl5_198
    | ~ spl5_148
    | ~ spl5_192 ),
    inference(avatar_split_clause,[],[f1804,f1769,f1343,f1830])).

fof(f1830,plain,
    ( spl5_198
  <=> k1_xboole_0 = sK3(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f1769,plain,
    ( spl5_192
  <=> v1_xboole_0(sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f1804,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0)
    | ~ spl5_148
    | ~ spl5_192 ),
    inference(unit_resulting_resolution,[],[f1344,f1770,f72])).

fof(f1770,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ spl5_192 ),
    inference(avatar_component_clause,[],[f1769])).

fof(f1800,plain,
    ( spl5_196
    | spl5_193 ),
    inference(avatar_split_clause,[],[f1772,f1766,f1798])).

fof(f1772,plain,
    ( r2_hidden(sK3(sK3(k1_xboole_0)),sK3(k1_xboole_0))
    | ~ spl5_193 ),
    inference(unit_resulting_resolution,[],[f65,f1767,f71])).

fof(f1789,plain,
    ( ~ spl5_195
    | spl5_193 ),
    inference(avatar_split_clause,[],[f1776,f1766,f1787])).

fof(f1787,plain,
    ( spl5_195
  <=> ~ m1_subset_1(sK3(k1_xboole_0),sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_195])])).

fof(f1776,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0),sK3(k1_xboole_0))
    | ~ spl5_193 ),
    inference(unit_resulting_resolution,[],[f1767,f132])).

fof(f1771,plain,
    ( ~ spl5_191
    | spl5_192
    | spl5_189 ),
    inference(avatar_split_clause,[],[f1756,f1752,f1769,f1763])).

fof(f1763,plain,
    ( spl5_191
  <=> ~ m1_subset_1(k1_xboole_0,sK3(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_191])])).

fof(f1756,plain,
    ( v1_xboole_0(sK3(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl5_189 ),
    inference(resolution,[],[f1753,f71])).

fof(f1754,plain,
    ( ~ spl5_189
    | spl5_13
    | ~ spl5_186 ),
    inference(avatar_split_clause,[],[f1738,f1735,f160,f1752])).

fof(f160,plain,
    ( spl5_13
  <=> u1_struct_0(sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f1735,plain,
    ( spl5_186
  <=> ! [X11,X10] :
        ( u1_struct_0(sK0) = X10
        | ~ r2_hidden(X10,X11)
        | ~ m1_subset_1(X11,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_186])])).

fof(f1738,plain,
    ( ~ r2_hidden(k1_xboole_0,sK3(k1_xboole_0))
    | ~ spl5_13
    | ~ spl5_186 ),
    inference(unit_resulting_resolution,[],[f65,f161,f1736])).

fof(f1736,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X11,X10)
        | ~ r2_hidden(X10,X11)
        | u1_struct_0(sK0) = X10 )
    | ~ spl5_186 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f161,plain,
    ( u1_struct_0(sK0) != k1_xboole_0
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f1737,plain,
    ( spl5_184
    | spl5_186
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1200,f86,f1735,f1732])).

fof(f1732,plain,
    ( spl5_184
  <=> ! [X13,X12] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k2_yellow_0(sK0,X12))
        | ~ r2_hidden(X13,k2_yellow_0(sK0,X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f1200,plain,
    ( ! [X12,X10,X13,X11] :
        ( u1_struct_0(sK0) = X10
        | ~ m1_subset_1(X11,X10)
        | ~ m1_subset_1(u1_struct_0(sK0),k2_yellow_0(sK0,X12))
        | ~ r2_hidden(X13,k2_yellow_0(sK0,X12))
        | ~ r2_hidden(X10,X11) )
    | ~ spl5_2 ),
    inference(resolution,[],[f1195,f104])).

fof(f104,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f87,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',dt_k2_yellow_0)).

fof(f1195,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X0)
      | X0 = X1
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X0,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X1,X3) ) ),
    inference(subsumption_resolution,[],[f1187,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t7_boole)).

fof(f1187,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X1
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X0,X2)
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X1,X3) ) ),
    inference(resolution,[],[f218,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t1_subset)).

fof(f218,plain,(
    ! [X21,X19,X17,X20,X18] :
      ( ~ m1_subset_1(X19,X20)
      | X17 = X19
      | ~ m1_subset_1(X18,X17)
      | ~ m1_subset_1(X20,X19)
      | v1_xboole_0(X20)
      | ~ m1_subset_1(X17,X18)
      | ~ r2_hidden(X21,X18) ) ),
    inference(resolution,[],[f154,f73])).

fof(f154,plain,(
    ! [X6,X4,X7,X5] :
      ( v1_xboole_0(X4)
      | ~ m1_subset_1(X5,X4)
      | X5 = X6
      | ~ m1_subset_1(X4,X5)
      | ~ m1_subset_1(X7,X6)
      | v1_xboole_0(X7)
      | ~ m1_subset_1(X6,X7) ) ),
    inference(resolution,[],[f128,f107])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | X1 = X2
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f107,f72])).

fof(f1726,plain,
    ( ~ spl5_61
    | spl5_182
    | spl5_13
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f335,f328,f160,f1724,f498])).

fof(f498,plain,
    ( spl5_61
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f1724,plain,
    ( spl5_182
  <=> ! [X0] :
        ( sK2(sK0,sK1,k1_xboole_0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_182])])).

fof(f328,plain,
    ( spl5_36
  <=> m1_subset_1(sK2(sK0,sK1,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f335,plain,
    ( ! [X0] :
        ( sK2(sK0,sK1,k1_xboole_0) = X0
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_13
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f333,f161])).

fof(f333,plain,
    ( ! [X0] :
        ( sK2(sK0,sK1,k1_xboole_0) = X0
        | ~ m1_subset_1(u1_struct_0(sK0),X0)
        | ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | u1_struct_0(sK0) = k1_xboole_0 )
    | ~ spl5_36 ),
    inference(resolution,[],[f329,f225])).

fof(f225,plain,(
    ! [X19,X20,X18] :
      ( ~ m1_subset_1(X20,X19)
      | X18 = X20
      | ~ m1_subset_1(X19,X18)
      | ~ m1_subset_1(X19,X20)
      | ~ m1_subset_1(X18,X19)
      | k1_xboole_0 = X19 ) ),
    inference(resolution,[],[f220,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t6_boole)).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | X1 = X2
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X0,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(factoring,[],[f154])).

fof(f329,plain,
    ( m1_subset_1(sK2(sK0,sK1,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f328])).

fof(f1671,plain,
    ( ~ spl5_181
    | spl5_173 ),
    inference(avatar_split_clause,[],[f1625,f1599,f1669])).

fof(f1669,plain,
    ( spl5_181
  <=> ~ r2_hidden(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))),sK3(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f1599,plain,
    ( spl5_173
  <=> ~ v1_xboole_0(sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f1625,plain,
    ( ~ r2_hidden(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))),sK3(sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))))
    | ~ spl5_173 ),
    inference(unit_resulting_resolution,[],[f65,f1600,f106])).

fof(f1600,plain,
    ( ~ v1_xboole_0(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))))
    | ~ spl5_173 ),
    inference(avatar_component_clause,[],[f1599])).

fof(f1652,plain,
    ( spl5_178
    | spl5_173 ),
    inference(avatar_split_clause,[],[f1621,f1599,f1650])).

fof(f1650,plain,
    ( spl5_178
  <=> r2_hidden(sK3(sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))),sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1621,plain,
    ( r2_hidden(sK3(sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))),sK3(sK3(sK3(sK3(u1_struct_0(sK0))))))
    | ~ spl5_173 ),
    inference(unit_resulting_resolution,[],[f65,f1600,f71])).

fof(f1643,plain,
    ( ~ spl5_177
    | spl5_173 ),
    inference(avatar_split_clause,[],[f1629,f1599,f1641])).

fof(f1641,plain,
    ( spl5_177
  <=> ~ m1_subset_1(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))),sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f1629,plain,
    ( ~ m1_subset_1(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))),sK3(sK3(sK3(sK3(u1_struct_0(sK0))))))
    | ~ spl5_173 ),
    inference(unit_resulting_resolution,[],[f1600,f132])).

fof(f1610,plain,
    ( spl5_172
    | ~ spl5_175
    | ~ spl5_104 ),
    inference(avatar_split_clause,[],[f958,f939,f1608,f1602])).

fof(f1602,plain,
    ( spl5_172
  <=> v1_xboole_0(sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f1608,plain,
    ( spl5_175
  <=> ~ m1_subset_1(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f939,plain,
    ( spl5_104
  <=> r2_hidden(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))),sK3(sK3(sK3(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f958,plain,
    ( ~ m1_subset_1(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(sK3(sK3(u1_struct_0(sK0))))))
    | v1_xboole_0(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))))
    | ~ spl5_104 ),
    inference(resolution,[],[f940,f106])).

fof(f940,plain,
    ( r2_hidden(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))),sK3(sK3(sK3(u1_struct_0(sK0)))))
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f939])).

fof(f1584,plain,
    ( ~ spl5_171
    | spl5_165 ),
    inference(avatar_split_clause,[],[f1575,f1544,f1582])).

fof(f1582,plain,
    ( spl5_171
  <=> ~ r2_hidden(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f1544,plain,
    ( spl5_165
  <=> ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f1575,plain,
    ( ~ r2_hidden(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl5_165 ),
    inference(unit_resulting_resolution,[],[f1545,f70])).

fof(f1545,plain,
    ( ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl5_165 ),
    inference(avatar_component_clause,[],[f1544])).

fof(f1559,plain,
    ( ~ spl5_169
    | spl5_157 ),
    inference(avatar_split_clause,[],[f1512,f1486,f1557])).

fof(f1557,plain,
    ( spl5_169
  <=> ~ r2_hidden(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))),sK3(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f1486,plain,
    ( spl5_157
  <=> ~ v1_xboole_0(sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f1512,plain,
    ( ~ r2_hidden(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))),sK3(sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))))
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f65,f1487,f106])).

fof(f1487,plain,
    ( ~ v1_xboole_0(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))))
    | ~ spl5_157 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f1552,plain,
    ( ~ spl5_165
    | ~ spl5_167
    | spl5_1
    | ~ spl5_2
    | spl5_111 ),
    inference(avatar_split_clause,[],[f1000,f972,f86,f79,f1550,f1544])).

fof(f1550,plain,
    ( spl5_167
  <=> ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f972,plain,
    ( spl5_111
  <=> ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f1000,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))))
    | ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_111 ),
    inference(forward_demodulation,[],[f999,f67])).

fof(f999,plain,
    ( ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_111 ),
    inference(resolution,[],[f973,f211])).

fof(f973,plain,
    ( ~ r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f972])).

fof(f1539,plain,
    ( spl5_162
    | spl5_157 ),
    inference(avatar_split_clause,[],[f1508,f1486,f1537])).

fof(f1537,plain,
    ( spl5_162
  <=> r2_hidden(sK3(sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))),sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_162])])).

fof(f1508,plain,
    ( r2_hidden(sK3(sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))),sK3(sK3(sK2(sK0,sK1,k1_xboole_0))))
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f65,f1487,f71])).

fof(f1530,plain,
    ( ~ spl5_161
    | spl5_157 ),
    inference(avatar_split_clause,[],[f1516,f1486,f1528])).

fof(f1528,plain,
    ( spl5_161
  <=> ~ m1_subset_1(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))),sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_161])])).

fof(f1516,plain,
    ( ~ m1_subset_1(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))),sK3(sK3(sK2(sK0,sK1,k1_xboole_0))))
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f1487,f132])).

fof(f1497,plain,
    ( spl5_156
    | ~ spl5_159
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f873,f841,f1495,f1489])).

fof(f1489,plain,
    ( spl5_156
  <=> v1_xboole_0(sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f1495,plain,
    ( spl5_159
  <=> ~ m1_subset_1(sK3(sK2(sK0,sK1,k1_xboole_0)),sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_159])])).

fof(f841,plain,
    ( spl5_94
  <=> r2_hidden(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))),sK3(sK2(sK0,sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f873,plain,
    ( ~ m1_subset_1(sK3(sK2(sK0,sK1,k1_xboole_0)),sK3(sK3(sK2(sK0,sK1,k1_xboole_0))))
    | v1_xboole_0(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))))
    | ~ spl5_94 ),
    inference(resolution,[],[f842,f106])).

fof(f842,plain,
    ( r2_hidden(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))),sK3(sK2(sK0,sK1,k1_xboole_0)))
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f841])).

fof(f1441,plain,
    ( spl5_152
    | spl5_154
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f1337,f199,f93,f1439,f1436])).

fof(f1436,plain,
    ( spl5_152
  <=> ! [X22,X23] :
        ( ~ m1_subset_1(k1_xboole_0,k2_yellow_0(sK4,X22))
        | ~ r2_hidden(X23,k2_yellow_0(sK4,X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).

fof(f1439,plain,
    ( spl5_154
  <=> ! [X20,X21] :
        ( k1_xboole_0 = X20
        | ~ r2_hidden(X20,X21)
        | ~ m1_subset_1(X21,X20) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f93,plain,
    ( spl5_4
  <=> l1_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f199,plain,
    ( spl5_20
  <=> u1_struct_0(sK4) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1337,plain,
    ( ! [X23,X21,X22,X20] :
        ( k1_xboole_0 = X20
        | ~ m1_subset_1(k1_xboole_0,k2_yellow_0(sK4,X22))
        | ~ m1_subset_1(X21,X20)
        | ~ r2_hidden(X23,k2_yellow_0(sK4,X22))
        | ~ r2_hidden(X20,X21) )
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f1328,f200])).

fof(f200,plain,
    ( u1_struct_0(sK4) = k1_xboole_0
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1328,plain,
    ( ! [X23,X21,X22,X20] :
        ( ~ m1_subset_1(k1_xboole_0,k2_yellow_0(sK4,X22))
        | u1_struct_0(sK4) = X20
        | ~ m1_subset_1(X21,X20)
        | ~ r2_hidden(X23,k2_yellow_0(sK4,X22))
        | ~ r2_hidden(X20,X21) )
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f200,f1303])).

fof(f1303,plain,
    ( ! [X23,X21,X22,X20] :
        ( u1_struct_0(sK4) = X20
        | ~ m1_subset_1(X21,X20)
        | ~ m1_subset_1(u1_struct_0(sK4),k2_yellow_0(sK4,X22))
        | ~ r2_hidden(X23,k2_yellow_0(sK4,X22))
        | ~ r2_hidden(X20,X21) )
    | ~ spl5_4 ),
    inference(resolution,[],[f105,f1195])).

fof(f105,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK4,X0),u1_struct_0(sK4))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f94,f68])).

fof(f94,plain,
    ( l1_orders_2(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f1377,plain,
    ( ~ spl5_151
    | ~ spl5_20
    | spl5_145 ),
    inference(avatar_split_clause,[],[f1320,f1290,f199,f1375])).

fof(f1375,plain,
    ( spl5_151
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_151])])).

fof(f1290,plain,
    ( spl5_145
  <=> ~ m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_145])])).

fof(f1320,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_145 ),
    inference(backward_demodulation,[],[f200,f1291])).

fof(f1291,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ spl5_145 ),
    inference(avatar_component_clause,[],[f1290])).

fof(f1345,plain,
    ( spl5_148
    | ~ spl5_20
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f1319,f1272,f199,f1343])).

fof(f1272,plain,
    ( spl5_142
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1319,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_20
    | ~ spl5_142 ),
    inference(backward_demodulation,[],[f200,f1273])).

fof(f1273,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f1316,plain,
    ( spl5_146
    | spl5_143 ),
    inference(avatar_split_clause,[],[f1278,f1275,f1314])).

fof(f1314,plain,
    ( spl5_146
  <=> r2_hidden(sK3(u1_struct_0(sK4)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f1275,plain,
    ( spl5_143
  <=> ~ v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_143])])).

fof(f1278,plain,
    ( r2_hidden(sK3(u1_struct_0(sK4)),u1_struct_0(sK4))
    | ~ spl5_143 ),
    inference(unit_resulting_resolution,[],[f65,f1276,f71])).

fof(f1276,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ spl5_143 ),
    inference(avatar_component_clause,[],[f1275])).

fof(f1292,plain,
    ( ~ spl5_145
    | spl5_143 ),
    inference(avatar_split_clause,[],[f1281,f1275,f1290])).

fof(f1281,plain,
    ( ~ m1_subset_1(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ spl5_143 ),
    inference(unit_resulting_resolution,[],[f1276,f132])).

fof(f1277,plain,
    ( ~ spl5_143
    | spl5_21 ),
    inference(avatar_split_clause,[],[f1270,f196,f1275])).

fof(f196,plain,
    ( spl5_21
  <=> u1_struct_0(sK4) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1270,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f197,f57])).

fof(f197,plain,
    ( u1_struct_0(sK4) != k1_xboole_0
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f1269,plain,
    ( spl5_138
    | spl5_140
    | ~ spl5_4
    | ~ spl5_20
    | ~ spl5_136 ),
    inference(avatar_split_clause,[],[f1246,f1234,f199,f93,f1267,f1264])).

fof(f1264,plain,
    ( spl5_138
  <=> ! [X9] : ~ r2_hidden(X9,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f1267,plain,
    ( spl5_140
  <=> ! [X8] :
        ( ~ r2_hidden(k1_xboole_0,k2_yellow_0(sK4,X8))
        | k2_yellow_0(sK4,X8) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f1234,plain,
    ( spl5_136
  <=> ! [X16,X15,X14] :
        ( k1_xboole_0 = X14
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X14,X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f1246,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(k1_xboole_0,k2_yellow_0(sK4,X8))
        | ~ r2_hidden(X9,k1_xboole_0)
        | k2_yellow_0(sK4,X8) = k1_xboole_0 )
    | ~ spl5_4
    | ~ spl5_20
    | ~ spl5_136 ),
    inference(resolution,[],[f1235,f205])).

fof(f205,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK4,X0),k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f200,f105])).

fof(f1235,plain,
    ( ! [X14,X15,X16] :
        ( ~ m1_subset_1(X14,X15)
        | ~ r2_hidden(X15,X14)
        | ~ r2_hidden(X16,X15)
        | k1_xboole_0 = X14 )
    | ~ spl5_136 ),
    inference(avatar_component_clause,[],[f1234])).

fof(f1236,plain,
    ( spl5_134
    | spl5_136
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f1213,f199,f93,f1234,f1231])).

fof(f1231,plain,
    ( spl5_134
  <=> ! [X17] : ~ r2_hidden(k1_xboole_0,k2_yellow_0(sK4,X17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f1213,plain,
    ( ! [X14,X17,X15,X16] :
        ( k1_xboole_0 = X14
        | ~ m1_subset_1(X14,X15)
        | ~ r2_hidden(X16,X15)
        | ~ r2_hidden(k1_xboole_0,k2_yellow_0(sK4,X17))
        | ~ r2_hidden(X15,X14) )
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(resolution,[],[f1198,f205])).

fof(f1198,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X1)
      | X0 = X1
      | ~ m1_subset_1(X0,X3)
      | ~ r2_hidden(X4,X3)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X3,X0) ) ),
    inference(resolution,[],[f1195,f70])).

fof(f1167,plain,
    ( spl5_132
    | ~ spl5_125
    | spl5_13
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f726,f717,f160,f1095,f1165])).

fof(f1165,plain,
    ( spl5_132
  <=> k1_xboole_0 = sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f1095,plain,
    ( spl5_125
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f726,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | k1_xboole_0 = sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)
    | ~ spl5_13
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f724,f161])).

fof(f724,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 = sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)
    | ~ spl5_82 ),
    inference(resolution,[],[f718,f140])).

fof(f140,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,X6)
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6 ) ),
    inference(resolution,[],[f130,f57])).

fof(f130,plain,(
    ! [X6,X7] :
      ( v1_xboole_0(X6)
      | ~ m1_subset_1(X6,X7)
      | ~ m1_subset_1(X7,X6)
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f107,f57])).

fof(f1147,plain,
    ( ~ spl5_131
    | spl5_123 ),
    inference(avatar_split_clause,[],[f1102,f1086,f1145])).

fof(f1145,plain,
    ( spl5_131
  <=> ~ r2_hidden(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),sK3(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f1086,plain,
    ( spl5_123
  <=> ~ v1_xboole_0(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_123])])).

fof(f1102,plain,
    ( ~ r2_hidden(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),sK3(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)))
    | ~ spl5_123 ),
    inference(unit_resulting_resolution,[],[f65,f1087,f106])).

fof(f1087,plain,
    ( ~ v1_xboole_0(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_123 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1140,plain,
    ( spl5_128
    | spl5_123 ),
    inference(avatar_split_clause,[],[f1098,f1086,f1138])).

fof(f1138,plain,
    ( spl5_128
  <=> r2_hidden(sK3(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f1098,plain,
    ( r2_hidden(sK3(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_123 ),
    inference(unit_resulting_resolution,[],[f65,f1087,f71])).

fof(f1121,plain,
    ( ~ spl5_127
    | spl5_123 ),
    inference(avatar_split_clause,[],[f1107,f1086,f1119])).

fof(f1119,plain,
    ( spl5_127
  <=> ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_127])])).

fof(f1107,plain,
    ( ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_123 ),
    inference(unit_resulting_resolution,[],[f1087,f132])).

fof(f1097,plain,
    ( spl5_122
    | ~ spl5_125
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f754,f733,f1095,f1089])).

fof(f1089,plain,
    ( spl5_122
  <=> v1_xboole_0(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f733,plain,
    ( spl5_84
  <=> r2_hidden(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f754,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | v1_xboole_0(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_84 ),
    inference(resolution,[],[f734,f106])).

fof(f734,plain,
    ( r2_hidden(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f733])).

fof(f1064,plain,
    ( ~ spl5_121
    | spl5_115 ),
    inference(avatar_split_clause,[],[f1027,f1018,f1062])).

fof(f1062,plain,
    ( spl5_121
  <=> ~ r2_hidden(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),sK3(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f1018,plain,
    ( spl5_115
  <=> ~ v1_xboole_0(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f1027,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),sK3(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))))
    | ~ spl5_115 ),
    inference(unit_resulting_resolution,[],[f65,f1019,f106])).

fof(f1019,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_115 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f1057,plain,
    ( spl5_118
    | spl5_115 ),
    inference(avatar_split_clause,[],[f1024,f1018,f1055])).

fof(f1055,plain,
    ( spl5_118
  <=> r2_hidden(sK3(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f1024,plain,
    ( r2_hidden(sK3(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_115 ),
    inference(unit_resulting_resolution,[],[f65,f1019,f71])).

fof(f1048,plain,
    ( ~ spl5_117
    | spl5_115 ),
    inference(avatar_split_clause,[],[f1028,f1018,f1046])).

fof(f1046,plain,
    ( spl5_117
  <=> ~ m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_117])])).

fof(f1028,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_115 ),
    inference(unit_resulting_resolution,[],[f1019,f132])).

fof(f1023,plain,
    ( ~ spl5_113
    | spl5_114
    | spl5_47 ),
    inference(avatar_split_clause,[],[f408,f395,f1021,f1015])).

fof(f1015,plain,
    ( spl5_113
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f1021,plain,
    ( spl5_114
  <=> v1_xboole_0(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f395,plain,
    ( spl5_47
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f408,plain,
    ( v1_xboole_0(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_47 ),
    inference(resolution,[],[f396,f71])).

fof(f396,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f395])).

fof(f977,plain,
    ( spl5_108
    | spl5_110
    | spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f847,f118,f86,f79,f975,f969])).

fof(f969,plain,
    ( spl5_108
  <=> k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k2_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f975,plain,
    ( spl5_110
  <=> r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f847,plain,
    ( r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0)))))
    | k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k2_yellow_0(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(factoring,[],[f782])).

fof(f782,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | r1_lattice3(sK0,k3_xboole_0(u1_struct_0(sK0),k3_xboole_0(sK1,u1_struct_0(sK0))),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f781,f67])).

fof(f781,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f780,f708])).

fof(f780,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f779,f80])).

fof(f779,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f776,f87])).

fof(f776,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | k2_yellow_0(sK0,X0) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | r1_lattice3(sK0,k3_xboole_0(k3_xboole_0(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
        | ~ m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(resolution,[],[f707,f60])).

fof(f948,plain,
    ( ~ spl5_107
    | spl5_99 ),
    inference(avatar_split_clause,[],[f909,f893,f946])).

fof(f946,plain,
    ( spl5_107
  <=> ~ r2_hidden(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(sK3(sK3(u1_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f893,plain,
    ( spl5_99
  <=> ~ v1_xboole_0(sK3(sK3(sK3(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f909,plain,
    ( ~ r2_hidden(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(sK3(sK3(u1_struct_0(sK0))))))
    | ~ spl5_99 ),
    inference(unit_resulting_resolution,[],[f65,f894,f106])).

fof(f894,plain,
    ( ~ v1_xboole_0(sK3(sK3(sK3(u1_struct_0(sK0)))))
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f893])).

fof(f941,plain,
    ( spl5_104
    | spl5_99 ),
    inference(avatar_split_clause,[],[f905,f893,f939])).

fof(f905,plain,
    ( r2_hidden(sK3(sK3(sK3(sK3(u1_struct_0(sK0))))),sK3(sK3(sK3(u1_struct_0(sK0)))))
    | ~ spl5_99 ),
    inference(unit_resulting_resolution,[],[f65,f894,f71])).

fof(f927,plain,
    ( ~ spl5_103
    | spl5_99 ),
    inference(avatar_split_clause,[],[f913,f893,f925])).

fof(f925,plain,
    ( spl5_103
  <=> ~ m1_subset_1(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(sK3(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f913,plain,
    ( ~ m1_subset_1(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(sK3(u1_struct_0(sK0)))))
    | ~ spl5_99 ),
    inference(unit_resulting_resolution,[],[f894,f132])).

fof(f904,plain,
    ( spl5_98
    | ~ spl5_101
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f666,f647,f902,f896])).

fof(f896,plain,
    ( spl5_98
  <=> v1_xboole_0(sK3(sK3(sK3(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f902,plain,
    ( spl5_101
  <=> ~ m1_subset_1(sK3(sK3(u1_struct_0(sK0))),sK3(sK3(sK3(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f647,plain,
    ( spl5_76
  <=> r2_hidden(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f666,plain,
    ( ~ m1_subset_1(sK3(sK3(u1_struct_0(sK0))),sK3(sK3(sK3(u1_struct_0(sK0)))))
    | v1_xboole_0(sK3(sK3(sK3(u1_struct_0(sK0)))))
    | ~ spl5_76 ),
    inference(resolution,[],[f648,f106])).

fof(f648,plain,
    ( r2_hidden(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(u1_struct_0(sK0))))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f647])).

fof(f862,plain,
    ( ~ spl5_97
    | spl5_89 ),
    inference(avatar_split_clause,[],[f815,f794,f860])).

fof(f860,plain,
    ( spl5_97
  <=> ~ r2_hidden(sK3(sK2(sK0,sK1,k1_xboole_0)),sK3(sK3(sK2(sK0,sK1,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f794,plain,
    ( spl5_89
  <=> ~ v1_xboole_0(sK3(sK2(sK0,sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_89])])).

fof(f815,plain,
    ( ~ r2_hidden(sK3(sK2(sK0,sK1,k1_xboole_0)),sK3(sK3(sK2(sK0,sK1,k1_xboole_0))))
    | ~ spl5_89 ),
    inference(unit_resulting_resolution,[],[f65,f795,f106])).

fof(f795,plain,
    ( ~ v1_xboole_0(sK3(sK2(sK0,sK1,k1_xboole_0)))
    | ~ spl5_89 ),
    inference(avatar_component_clause,[],[f794])).

fof(f843,plain,
    ( spl5_94
    | spl5_89 ),
    inference(avatar_split_clause,[],[f811,f794,f841])).

fof(f811,plain,
    ( r2_hidden(sK3(sK3(sK2(sK0,sK1,k1_xboole_0))),sK3(sK2(sK0,sK1,k1_xboole_0)))
    | ~ spl5_89 ),
    inference(unit_resulting_resolution,[],[f65,f795,f71])).

fof(f834,plain,
    ( ~ spl5_93
    | spl5_89 ),
    inference(avatar_split_clause,[],[f820,f794,f832])).

fof(f832,plain,
    ( spl5_93
  <=> ~ m1_subset_1(sK3(sK2(sK0,sK1,k1_xboole_0)),sK3(sK2(sK0,sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f820,plain,
    ( ~ m1_subset_1(sK3(sK2(sK0,sK1,k1_xboole_0)),sK3(sK2(sK0,sK1,k1_xboole_0)))
    | ~ spl5_89 ),
    inference(unit_resulting_resolution,[],[f795,f132])).

fof(f805,plain,
    ( spl5_88
    | ~ spl5_91
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f557,f537,f803,f797])).

fof(f797,plain,
    ( spl5_88
  <=> v1_xboole_0(sK3(sK2(sK0,sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f803,plain,
    ( spl5_91
  <=> ~ m1_subset_1(sK2(sK0,sK1,k1_xboole_0),sK3(sK2(sK0,sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f537,plain,
    ( spl5_64
  <=> r2_hidden(sK3(sK2(sK0,sK1,k1_xboole_0)),sK2(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f557,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_xboole_0),sK3(sK2(sK0,sK1,k1_xboole_0)))
    | v1_xboole_0(sK3(sK2(sK0,sK1,k1_xboole_0)))
    | ~ spl5_64 ),
    inference(resolution,[],[f538,f106])).

fof(f538,plain,
    ( r2_hidden(sK3(sK2(sK0,sK1,k1_xboole_0)),sK2(sK0,sK1,k1_xboole_0))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f537])).

fof(f787,plain,
    ( spl5_14
    | spl5_12
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f208,f86,f163,f166])).

fof(f166,plain,
    ( spl5_14
  <=> ! [X5] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k2_yellow_0(sK0,X5))
        | k2_yellow_0(sK0,X5) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f163,plain,
    ( spl5_12
  <=> u1_struct_0(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f208,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = k1_xboole_0
        | k2_yellow_0(sK0,X0) = k1_xboole_0
        | ~ m1_subset_1(u1_struct_0(sK0),k2_yellow_0(sK0,X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f145,f87])).

fof(f145,plain,(
    ! [X4,X3] :
      ( ~ l1_orders_2(X3)
      | u1_struct_0(X3) = k1_xboole_0
      | k2_yellow_0(X3,X4) = k1_xboole_0
      | ~ m1_subset_1(u1_struct_0(X3),k2_yellow_0(X3,X4)) ) ),
    inference(resolution,[],[f140,f68])).

fof(f742,plain,
    ( ~ spl5_87
    | spl5_27
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f722,f717,f250,f740])).

fof(f740,plain,
    ( spl5_87
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f250,plain,
    ( spl5_27
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f722,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ spl5_27
    | ~ spl5_82 ),
    inference(unit_resulting_resolution,[],[f251,f718,f106])).

fof(f251,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f250])).

fof(f735,plain,
    ( spl5_84
    | spl5_27
    | ~ spl5_82 ),
    inference(avatar_split_clause,[],[f721,f717,f250,f733])).

fof(f721,plain,
    ( r2_hidden(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl5_27
    | ~ spl5_82 ),
    inference(unit_resulting_resolution,[],[f251,f718,f71])).

fof(f719,plain,
    ( spl5_82
    | spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | spl5_11 ),
    inference(avatar_split_clause,[],[f705,f125,f118,f86,f79,f717])).

fof(f705,plain,
    ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f80,f87,f126,f119,f62])).

fof(f703,plain,
    ( spl5_43
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f702])).

fof(f702,plain,
    ( $false
    | ~ spl5_43
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f364,f400])).

fof(f400,plain,
    ( m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f389,f70])).

fof(f389,plain,
    ( r2_hidden(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f388])).

fof(f388,plain,
    ( spl5_44
  <=> r2_hidden(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f364,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl5_43
  <=> ~ m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f696,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_11
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(avatar_contradiction_clause,[],[f695])).

fof(f695,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f694,f80])).

fof(f694,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f693,f87])).

fof(f693,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f692,f113])).

fof(f113,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_6
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f692,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_11
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f691,f684])).

fof(f684,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(unit_resulting_resolution,[],[f80,f87,f367,f680,f61])).

fof(f680,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl5_80
  <=> r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f367,plain,
    ( m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl5_42
  <=> m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f691,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_11
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f686,f126])).

fof(f686,plain,
    ( k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_80 ),
    inference(resolution,[],[f680,f64])).

fof(f690,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_11
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(avatar_contradiction_clause,[],[f689])).

fof(f689,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_42
    | ~ spl5_80 ),
    inference(subsumption_resolution,[],[f683,f684])).

fof(f683,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_80 ),
    inference(unit_resulting_resolution,[],[f80,f87,f113,f126,f680,f64])).

fof(f681,plain,
    ( spl5_80
    | spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_11 ),
    inference(avatar_split_clause,[],[f640,f125,f112,f86,f79,f679])).

fof(f640,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f632,f126])).

fof(f632,plain,
    ( r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(factoring,[],[f565])).

fof(f565,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,X0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f564,f455])).

fof(f455,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f236,f113])).

fof(f564,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,X0))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f563,f80])).

fof(f563,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,X0))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f560,f87])).

fof(f560,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,X0))
        | ~ m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f485,f60])).

fof(f485,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK2(sK0,sK1,X0))
        | k2_yellow_0(sK0,sK1) = k2_yellow_0(sK0,X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f322,f113])).

fof(f656,plain,
    ( ~ spl5_79
    | spl5_71 ),
    inference(avatar_split_clause,[],[f611,f595,f654])).

fof(f654,plain,
    ( spl5_79
  <=> ~ r2_hidden(sK3(sK3(u1_struct_0(sK0))),sK3(sK3(sK3(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f595,plain,
    ( spl5_71
  <=> ~ v1_xboole_0(sK3(sK3(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f611,plain,
    ( ~ r2_hidden(sK3(sK3(u1_struct_0(sK0))),sK3(sK3(sK3(u1_struct_0(sK0)))))
    | ~ spl5_71 ),
    inference(unit_resulting_resolution,[],[f65,f596,f106])).

fof(f596,plain,
    ( ~ v1_xboole_0(sK3(sK3(u1_struct_0(sK0))))
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f595])).

fof(f649,plain,
    ( spl5_76
    | spl5_71 ),
    inference(avatar_split_clause,[],[f607,f595,f647])).

fof(f607,plain,
    ( r2_hidden(sK3(sK3(sK3(u1_struct_0(sK0)))),sK3(sK3(u1_struct_0(sK0))))
    | ~ spl5_71 ),
    inference(unit_resulting_resolution,[],[f65,f596,f71])).

fof(f629,plain,
    ( ~ spl5_75
    | spl5_71 ),
    inference(avatar_split_clause,[],[f615,f595,f627])).

fof(f627,plain,
    ( spl5_75
  <=> ~ m1_subset_1(sK3(sK3(u1_struct_0(sK0))),sK3(sK3(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f615,plain,
    ( ~ m1_subset_1(sK3(sK3(u1_struct_0(sK0))),sK3(sK3(u1_struct_0(sK0))))
    | ~ spl5_71 ),
    inference(unit_resulting_resolution,[],[f596,f132])).

fof(f606,plain,
    ( spl5_70
    | ~ spl5_73
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f482,f462,f604,f598])).

fof(f598,plain,
    ( spl5_70
  <=> v1_xboole_0(sK3(sK3(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f604,plain,
    ( spl5_73
  <=> ~ m1_subset_1(sK3(u1_struct_0(sK0)),sK3(sK3(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f462,plain,
    ( spl5_54
  <=> r2_hidden(sK3(sK3(u1_struct_0(sK0))),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f482,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK0)),sK3(sK3(u1_struct_0(sK0))))
    | v1_xboole_0(sK3(sK3(u1_struct_0(sK0))))
    | ~ spl5_54 ),
    inference(resolution,[],[f463,f106])).

fof(f463,plain,
    ( r2_hidden(sK3(sK3(u1_struct_0(sK0))),sK3(u1_struct_0(sK0)))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f462])).

fof(f581,plain,
    ( spl5_68
    | ~ spl5_61
    | spl5_13
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f336,f328,f160,f498,f579])).

fof(f579,plain,
    ( spl5_68
  <=> k1_xboole_0 = sK2(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f336,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0))
    | k1_xboole_0 = sK2(sK0,sK1,k1_xboole_0)
    | ~ spl5_13
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f334,f161])).

fof(f334,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0))
    | u1_struct_0(sK0) = k1_xboole_0
    | k1_xboole_0 = sK2(sK0,sK1,k1_xboole_0)
    | ~ spl5_36 ),
    inference(resolution,[],[f329,f140])).

fof(f546,plain,
    ( ~ spl5_67
    | spl5_59 ),
    inference(avatar_split_clause,[],[f505,f489,f544])).

fof(f544,plain,
    ( spl5_67
  <=> ~ r2_hidden(sK2(sK0,sK1,k1_xboole_0),sK3(sK2(sK0,sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f489,plain,
    ( spl5_59
  <=> ~ v1_xboole_0(sK2(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f505,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k1_xboole_0),sK3(sK2(sK0,sK1,k1_xboole_0)))
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f65,f490,f106])).

fof(f490,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1,k1_xboole_0))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f489])).

fof(f539,plain,
    ( spl5_64
    | spl5_59 ),
    inference(avatar_split_clause,[],[f501,f489,f537])).

fof(f501,plain,
    ( r2_hidden(sK3(sK2(sK0,sK1,k1_xboole_0)),sK2(sK0,sK1,k1_xboole_0))
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f65,f490,f71])).

fof(f530,plain,
    ( ~ spl5_63
    | spl5_59 ),
    inference(avatar_split_clause,[],[f510,f489,f528])).

fof(f528,plain,
    ( spl5_63
  <=> ~ m1_subset_1(sK2(sK0,sK1,k1_xboole_0),sK2(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f510,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_xboole_0),sK2(sK0,sK1,k1_xboole_0))
    | ~ spl5_59 ),
    inference(unit_resulting_resolution,[],[f490,f132])).

fof(f500,plain,
    ( spl5_58
    | ~ spl5_61
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f359,f341,f498,f492])).

fof(f492,plain,
    ( spl5_58
  <=> v1_xboole_0(sK2(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f341,plain,
    ( spl5_38
  <=> r2_hidden(sK2(sK0,sK1,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f359,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0))
    | v1_xboole_0(sK2(sK0,sK1,k1_xboole_0))
    | ~ spl5_38 ),
    inference(resolution,[],[f342,f106])).

fof(f342,plain,
    ( r2_hidden(sK2(sK0,sK1,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f341])).

fof(f471,plain,
    ( ~ spl5_57
    | spl5_49 ),
    inference(avatar_split_clause,[],[f433,f417,f469])).

fof(f469,plain,
    ( spl5_57
  <=> ~ r2_hidden(sK3(u1_struct_0(sK0)),sK3(sK3(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f417,plain,
    ( spl5_49
  <=> ~ v1_xboole_0(sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f433,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(sK0)),sK3(sK3(u1_struct_0(sK0))))
    | ~ spl5_49 ),
    inference(unit_resulting_resolution,[],[f65,f418,f106])).

fof(f418,plain,
    ( ~ v1_xboole_0(sK3(u1_struct_0(sK0)))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f417])).

fof(f464,plain,
    ( spl5_54
    | spl5_49 ),
    inference(avatar_split_clause,[],[f429,f417,f462])).

fof(f429,plain,
    ( r2_hidden(sK3(sK3(u1_struct_0(sK0))),sK3(u1_struct_0(sK0)))
    | ~ spl5_49 ),
    inference(unit_resulting_resolution,[],[f65,f418,f71])).

fof(f452,plain,
    ( ~ spl5_53
    | spl5_49 ),
    inference(avatar_split_clause,[],[f438,f417,f450])).

fof(f450,plain,
    ( spl5_53
  <=> ~ m1_subset_1(sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f438,plain,
    ( ~ m1_subset_1(sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | ~ spl5_49 ),
    inference(unit_resulting_resolution,[],[f418,f132])).

fof(f428,plain,
    ( spl5_48
    | ~ spl5_51
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f319,f290,f426,f420])).

fof(f420,plain,
    ( spl5_48
  <=> v1_xboole_0(sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f426,plain,
    ( spl5_51
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f290,plain,
    ( spl5_32
  <=> r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f319,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | v1_xboole_0(sK3(u1_struct_0(sK0)))
    | ~ spl5_32 ),
    inference(resolution,[],[f291,f106])).

fof(f291,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f290])).

fof(f397,plain,
    ( ~ spl5_47
    | spl5_27
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f370,f366,f250,f395])).

fof(f370,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ spl5_27
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f251,f367,f106])).

fof(f390,plain,
    ( spl5_44
    | spl5_27
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f369,f366,f250,f388])).

fof(f369,plain,
    ( r2_hidden(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_27
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f251,f367,f71])).

fof(f368,plain,
    ( spl5_42
    | spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_11 ),
    inference(avatar_split_clause,[],[f285,f125,f112,f86,f79,f366])).

fof(f285,plain,
    ( m1_subset_1(sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f80,f87,f113,f126,f62])).

fof(f350,plain,
    ( ~ spl5_41
    | spl5_27
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f332,f328,f250,f348])).

fof(f348,plain,
    ( spl5_41
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f332,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(sK0,sK1,k1_xboole_0))
    | ~ spl5_27
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f251,f329,f106])).

fof(f343,plain,
    ( spl5_38
    | spl5_27
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f331,f328,f250,f341])).

fof(f331,plain,
    ( r2_hidden(sK2(sK0,sK1,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_27
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f251,f329,f71])).

fof(f330,plain,
    ( spl5_36
    | spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | spl5_19 ),
    inference(avatar_split_clause,[],[f233,f192,f112,f86,f79,f328])).

fof(f192,plain,
    ( spl5_19
  <=> k2_yellow_0(sK0,k1_xboole_0) != k2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f233,plain,
    ( m1_subset_1(sK2(sK0,sK1,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f80,f87,f113,f193,f62])).

fof(f193,plain,
    ( k2_yellow_0(sK0,k1_xboole_0) != k2_yellow_0(sK0,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f299,plain,
    ( ~ spl5_35
    | spl5_27 ),
    inference(avatar_split_clause,[],[f255,f250,f297])).

fof(f297,plain,
    ( spl5_35
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f255,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(u1_struct_0(sK0)))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f65,f251,f106])).

fof(f292,plain,
    ( spl5_32
    | spl5_27 ),
    inference(avatar_split_clause,[],[f253,f250,f290])).

fof(f253,plain,
    ( r2_hidden(sK3(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f65,f251,f71])).

fof(f283,plain,
    ( ~ spl5_31
    | spl5_25 ),
    inference(avatar_split_clause,[],[f275,f239,f281])).

fof(f281,plain,
    ( spl5_31
  <=> ~ r2_hidden(sK2(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f239,plain,
    ( spl5_25
  <=> ~ m1_subset_1(sK2(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f275,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f240,f70])).

fof(f240,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f239])).

fof(f267,plain,
    ( ~ spl5_29
    | spl5_27 ),
    inference(avatar_split_clause,[],[f256,f250,f265])).

fof(f265,plain,
    ( spl5_29
  <=> ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f256,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f251,f132])).

fof(f252,plain,
    ( ~ spl5_27
    | spl5_13 ),
    inference(avatar_split_clause,[],[f245,f160,f250])).

fof(f245,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f161,f57])).

fof(f244,plain,
    ( spl5_24
    | spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12
    | spl5_19 ),
    inference(avatar_split_clause,[],[f235,f192,f163,f112,f86,f79,f242])).

fof(f242,plain,
    ( spl5_24
  <=> m1_subset_1(sK2(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f235,plain,
    ( m1_subset_1(sK2(sK0,sK1,k1_xboole_0),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f233,f164])).

fof(f164,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f204,plain,
    ( spl5_20
    | spl5_22
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f147,f93,f202,f199])).

fof(f202,plain,
    ( spl5_22
  <=> ! [X6] :
        ( ~ m1_subset_1(u1_struct_0(sK4),k2_yellow_0(sK4,X6))
        | k2_yellow_0(sK4,X6) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f147,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(u1_struct_0(sK4),k2_yellow_0(sK4,X6))
        | u1_struct_0(sK4) = k1_xboole_0
        | k2_yellow_0(sK4,X6) = k1_xboole_0 )
    | ~ spl5_4 ),
    inference(resolution,[],[f140,f105])).

fof(f194,plain,
    ( ~ spl5_19
    | spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f174,f163,f125,f192])).

fof(f174,plain,
    ( k2_yellow_0(sK0,k1_xboole_0) != k2_yellow_0(sK0,sK1)
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f171,f56])).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t2_boole)).

fof(f171,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f164,f126])).

fof(f183,plain,
    ( spl5_16
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f173,f163,f118,f181])).

fof(f181,plain,
    ( spl5_16
  <=> r2_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f173,plain,
    ( r2_yellow_0(sK0,k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f170,f56])).

fof(f170,plain,
    ( r2_yellow_0(sK0,k3_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f164,f119])).

fof(f168,plain,
    ( spl5_12
    | spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f146,f86,f166,f163])).

fof(f146,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k2_yellow_0(sK0,X5))
        | u1_struct_0(sK0) = k1_xboole_0
        | k2_yellow_0(sK0,X5) = k1_xboole_0 )
    | ~ spl5_2 ),
    inference(resolution,[],[f140,f104])).

fof(f127,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f55,f125])).

fof(f55,plain,(
    k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k2_yellow_0(sK0,sK1) != k2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    & ( r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | r2_yellow_0(sK0,sK1) )
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r2_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k2_yellow_0(sK0,X1) != k2_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
          & ( r2_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
            | r2_yellow_0(sK0,X1) ) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) ) )
     => ( k2_yellow_0(X0,sK1) != k2_yellow_0(X0,k3_xboole_0(sK1,u1_struct_0(X0)))
        & ( r2_yellow_0(X0,k3_xboole_0(sK1,u1_struct_0(X0)))
          | r2_yellow_0(X0,sK1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow_0(X0,X1) != k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',t52_yellow_0)).

fof(f120,plain,
    ( spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f54,f118,f112])).

fof(f54,plain,
    ( r2_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f74,f93])).

fof(f74,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f50])).

fof(f50,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK4) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t52_yellow_0.p',existence_l1_orders_2)).

fof(f88,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f53,f86])).

fof(f53,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f52,f79])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
