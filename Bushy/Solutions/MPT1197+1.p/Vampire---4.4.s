%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t23_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:00 EDT 2019

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  286 ( 880 expanded)
%              Number of leaves         :   82 ( 408 expanded)
%              Depth                    :   12
%              Number of atoms          :  937 (2829 expanded)
%              Number of equality atoms :   54 ( 123 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2891,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f145,f152,f159,f166,f173,f180,f187,f194,f205,f212,f219,f226,f239,f246,f253,f260,f267,f274,f281,f320,f327,f334,f344,f351,f362,f369,f378,f390,f399,f407,f414,f423,f440,f447,f454,f461,f564,f571,f627,f634,f743,f750,f757,f764,f1222,f1461,f1468,f1475,f1482,f2502,f2511,f2518,f2525,f2766])).

fof(f2766,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | spl9_39
    | ~ spl9_86
    | ~ spl9_106 ),
    inference(avatar_contradiction_clause,[],[f2765])).

fof(f2765,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_39
    | ~ spl9_86
    | ~ spl9_106 ),
    inference(subsumption_resolution,[],[f2760,f1041])).

fof(f1041,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) != sK1
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_39
    | ~ spl9_86 ),
    inference(unit_resulting_resolution,[],[f137,f211,f186,f280,f756,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',d3_lattices)).

fof(f756,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_86 ),
    inference(avatar_component_clause,[],[f755])).

fof(f755,plain,
    ( spl9_86
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f280,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl9_39
  <=> ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f186,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl9_14
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f211,plain,
    ( l2_lattices(sK0)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl9_20
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f137,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2760,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) = sK1
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_106 ),
    inference(backward_demodulation,[],[f2633,f2524])).

fof(f2524,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1) = sK1
    | ~ spl9_106 ),
    inference(avatar_component_clause,[],[f2523])).

fof(f2523,plain,
    ( spl9_106
  <=> k1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f2633,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f186,f193,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',commutativity_k4_lattices)).

fof(f193,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl9_16
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f204,plain,
    ( l1_lattices(sK0)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl9_18
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f144,plain,
    ( v6_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl9_2
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f2525,plain,
    ( spl9_106
    | spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f2093,f1466,f203,f192,f185,f143,f136,f2523])).

fof(f1466,plain,
    ( spl9_94
  <=> k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f2093,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK1),sK1) = sK1
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_94 ),
    inference(backward_demodulation,[],[f1680,f1467])).

fof(f1467,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) = sK1
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1680,plain,
    ( k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f193,f186,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',redefinition_k4_lattices)).

fof(f2518,plain,
    ( spl9_104
    | spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f1969,f1473,f203,f192,f185,f143,f136,f2516])).

fof(f2516,plain,
    ( spl9_104
  <=> k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f1473,plain,
    ( spl9_96
  <=> k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f1969,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) = sK2
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_96 ),
    inference(backward_demodulation,[],[f1694,f1474])).

fof(f1474,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) = sK2
    | ~ spl9_96 ),
    inference(avatar_component_clause,[],[f1473])).

fof(f1694,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f186,f193,f121])).

fof(f2511,plain,
    ( spl9_102
    | spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f1859,f1480,f203,f192,f143,f136,f2509])).

fof(f2509,plain,
    ( spl9_102
  <=> k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f1480,plain,
    ( spl9_98
  <=> k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f1859,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK2,sK2),sK2) = sK2
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_98 ),
    inference(backward_demodulation,[],[f1695,f1481])).

fof(f1481,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK2) = sK2
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1695,plain,
    ( k4_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f193,f193,f121])).

fof(f2502,plain,
    ( spl9_100
    | spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_74
    | ~ spl9_92 ),
    inference(avatar_split_clause,[],[f2188,f1459,f562,f210,f203,f185,f143,f136,f2500])).

fof(f2500,plain,
    ( spl9_100
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f562,plain,
    ( spl9_74
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f1459,plain,
    ( spl9_92
  <=> k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f2188,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_20
    | ~ spl9_74
    | ~ spl9_92 ),
    inference(backward_demodulation,[],[f1679,f1483])).

fof(f1483,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1)
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_20
    | ~ spl9_74
    | ~ spl9_92 ),
    inference(unit_resulting_resolution,[],[f137,f211,f186,f563,f1460,f113])).

fof(f1460,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ spl9_92 ),
    inference(avatar_component_clause,[],[f1459])).

fof(f563,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f562])).

fof(f1679,plain,
    ( k4_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f186,f186,f121])).

fof(f1482,plain,
    ( spl9_98
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f1431,f192,f157,f150,f136,f1480])).

fof(f150,plain,
    ( spl9_4
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f157,plain,
    ( spl9_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f1431,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK2),sK2) = sK2
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f137,f158,f151,f193,f193,f108])).

fof(f108,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) != sK4(X0)
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f79,f81,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK4(X0)),sK4(X0)) != sK4(X0)
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',d8_lattices)).

fof(f151,plain,
    ( v8_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f150])).

fof(f158,plain,
    ( l3_lattices(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f1475,plain,
    ( spl9_96
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f1430,f192,f185,f157,f150,f136,f1473])).

fof(f1430,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) = sK2
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f137,f158,f151,f186,f193,f108])).

fof(f1468,plain,
    ( spl9_94
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f1416,f192,f185,f157,f150,f136,f1466])).

fof(f1416,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1) = sK1
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f137,f158,f151,f193,f186,f108])).

fof(f1461,plain,
    ( spl9_92
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f1415,f185,f157,f150,f136,f1459])).

fof(f1415,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f137,f158,f151,f186,f186,f108])).

fof(f1222,plain,
    ( spl9_90
    | spl9_1
    | ~ spl9_14
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f427,f210,f185,f136,f1220])).

fof(f1220,plain,
    ( spl9_90
  <=> m1_subset_1(k1_lattices(sK0,sK5(u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f427,plain,
    ( m1_subset_1(k1_lattices(sK0,sK5(u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f137,f211,f114,f186,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',dt_k1_lattices)).

fof(f114,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',existence_m1_subset_1)).

fof(f764,plain,
    ( spl9_88
    | spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f580,f203,f192,f143,f136,f762])).

fof(f762,plain,
    ( spl9_88
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f580,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f193,f193,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
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
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',dt_k4_lattices)).

fof(f757,plain,
    ( spl9_86
    | spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f579,f203,f192,f185,f143,f136,f755])).

fof(f579,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f186,f193,f120])).

fof(f750,plain,
    ( spl9_84
    | spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f573,f203,f192,f185,f143,f136,f748])).

fof(f748,plain,
    ( spl9_84
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f573,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f193,f186,f120])).

fof(f743,plain,
    ( spl9_82
    | spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f572,f203,f185,f143,f136,f741])).

fof(f741,plain,
    ( spl9_82
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f572,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f204,f186,f186,f120])).

fof(f634,plain,
    ( spl9_80
    | spl9_1
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f475,f203,f192,f136,f632])).

fof(f632,plain,
    ( spl9_80
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f475,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f204,f193,f193,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',dt_k2_lattices)).

fof(f627,plain,
    ( spl9_78
    | spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f474,f203,f192,f185,f136,f625])).

fof(f625,plain,
    ( spl9_78
  <=> m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f474,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f204,f186,f193,f124])).

fof(f571,plain,
    ( spl9_76
    | spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f471,f203,f192,f185,f136,f569])).

fof(f569,plain,
    ( spl9_76
  <=> m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f471,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f204,f193,f186,f124])).

fof(f564,plain,
    ( spl9_74
    | spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f470,f203,f185,f136,f562])).

fof(f470,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f137,f204,f186,f186,f124])).

fof(f461,plain,
    ( spl9_72
    | spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f429,f210,f192,f136,f459])).

fof(f459,plain,
    ( spl9_72
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f429,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f137,f211,f193,f193,f123])).

fof(f454,plain,
    ( spl9_70
    | spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f428,f210,f192,f185,f136,f452])).

fof(f452,plain,
    ( spl9_70
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f428,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f137,f211,f186,f193,f123])).

fof(f447,plain,
    ( spl9_68
    | spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f426,f210,f192,f185,f136,f445])).

fof(f445,plain,
    ( spl9_68
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f426,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f137,f211,f193,f186,f123])).

fof(f440,plain,
    ( spl9_66
    | spl9_1
    | ~ spl9_14
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f425,f210,f185,f136,f438])).

fof(f438,plain,
    ( spl9_66
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f425,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_14
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f137,f211,f186,f186,f123])).

fof(f423,plain,
    ( ~ spl9_65
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f415,f405,f421])).

fof(f421,plain,
    ( spl9_65
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f405,plain,
    ( spl9_60
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f415,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u2_lattices(sK0))
    | ~ spl9_60 ),
    inference(unit_resulting_resolution,[],[f406,f292])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f291,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',t5_subset)).

fof(f291,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f290,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',t4_subset)).

fof(f290,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f284])).

fof(f284,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f283,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',t2_subset)).

fof(f283,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f117,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',antisymmetry_r2_hidden)).

fof(f406,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f405])).

fof(f414,plain,
    ( spl9_62
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f380,f203,f412])).

fof(f412,plain,
    ( spl9_62
  <=> m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f380,plain,
    ( m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f204,f107])).

fof(f107,plain,(
    ! [X0] :
      ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',dt_u1_lattices)).

fof(f407,plain,
    ( spl9_60
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f353,f210,f405])).

fof(f353,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f211,f104])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',dt_u2_lattices)).

fof(f399,plain,
    ( ~ spl9_59
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f391,f388,f397])).

fof(f397,plain,
    ( spl9_59
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)),u1_lattices(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f388,plain,
    ( spl9_56
  <=> m1_subset_1(u1_lattices(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f391,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)),u1_lattices(sK8))
    | ~ spl9_56 ),
    inference(unit_resulting_resolution,[],[f389,f292])).

fof(f389,plain,
    ( m1_subset_1(u1_lattices(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))))
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( spl9_56
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f379,f178,f388])).

fof(f178,plain,
    ( spl9_12
  <=> l1_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f379,plain,
    ( m1_subset_1(u1_lattices(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))))
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f179,f107])).

fof(f179,plain,
    ( l1_lattices(sK8)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f378,plain,
    ( ~ spl9_55
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f370,f367,f376])).

fof(f376,plain,
    ( spl9_55
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7)),u2_lattices(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f367,plain,
    ( spl9_52
  <=> m1_subset_1(u2_lattices(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f370,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7)),u2_lattices(sK7))
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f368,f292])).

fof(f368,plain,
    ( m1_subset_1(u2_lattices(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f367])).

fof(f369,plain,
    ( spl9_52
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f352,f171,f367])).

fof(f171,plain,
    ( spl9_10
  <=> l2_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f352,plain,
    ( m1_subset_1(u2_lattices(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))))
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f172,f104])).

fof(f172,plain,
    ( l2_lattices(sK7)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f362,plain,
    ( spl9_50
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f337,f217,f360])).

fof(f360,plain,
    ( spl9_50
  <=> v1_funct_2(u1_lattices(sK6),k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f217,plain,
    ( spl9_22
  <=> l1_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f337,plain,
    ( v1_funct_2(u1_lattices(sK6),k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f218,f106])).

fof(f106,plain,(
    ! [X0] :
      ( v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f218,plain,
    ( l1_lattices(sK6)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f217])).

fof(f351,plain,
    ( spl9_48
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f336,f203,f349])).

fof(f349,plain,
    ( spl9_48
  <=> v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f336,plain,
    ( v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f204,f106])).

fof(f344,plain,
    ( spl9_46
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f335,f178,f342])).

fof(f342,plain,
    ( spl9_46
  <=> v1_funct_2(u1_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f335,plain,
    ( v1_funct_2(u1_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f179,f106])).

fof(f334,plain,
    ( spl9_44
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f313,f224,f332])).

fof(f332,plain,
    ( spl9_44
  <=> v1_funct_2(u2_lattices(sK6),k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f224,plain,
    ( spl9_24
  <=> l2_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f313,plain,
    ( v1_funct_2(u2_lattices(sK6),k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ spl9_24 ),
    inference(unit_resulting_resolution,[],[f225,f103])).

fof(f103,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f225,plain,
    ( l2_lattices(sK6)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f224])).

fof(f327,plain,
    ( spl9_42
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f312,f210,f325])).

fof(f325,plain,
    ( spl9_42
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f312,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f211,f103])).

fof(f320,plain,
    ( spl9_40
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f311,f171,f318])).

fof(f318,plain,
    ( spl9_40
  <=> v1_funct_2(u2_lattices(sK7),k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f311,plain,
    ( v1_funct_2(u2_lattices(sK7),k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f172,f103])).

fof(f281,plain,(
    ~ spl9_39 ),
    inference(avatar_split_clause,[],[f98,f279])).

fof(f98,plain,(
    ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f76,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(sK0,k4_lattices(sK0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r1_lattices(X0,k4_lattices(X0,sK1,X2),sK1)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,k4_lattices(X0,X1,sK2),X1)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',t23_lattices)).

fof(f274,plain,
    ( spl9_36
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f232,f217,f272])).

fof(f272,plain,
    ( spl9_36
  <=> v1_funct_1(u1_lattices(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f232,plain,
    ( v1_funct_1(u1_lattices(sK6))
    | ~ spl9_22 ),
    inference(unit_resulting_resolution,[],[f218,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f267,plain,
    ( spl9_34
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f229,f224,f265])).

fof(f265,plain,
    ( spl9_34
  <=> v1_funct_1(u2_lattices(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f229,plain,
    ( v1_funct_1(u2_lattices(sK6))
    | ~ spl9_24 ),
    inference(unit_resulting_resolution,[],[f225,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f260,plain,
    ( spl9_32
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f231,f203,f258])).

fof(f258,plain,
    ( spl9_32
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f231,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl9_18 ),
    inference(unit_resulting_resolution,[],[f204,f105])).

fof(f253,plain,
    ( spl9_30
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f228,f210,f251])).

fof(f251,plain,
    ( spl9_30
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f228,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl9_20 ),
    inference(unit_resulting_resolution,[],[f211,f102])).

fof(f246,plain,
    ( spl9_28
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f230,f178,f244])).

fof(f244,plain,
    ( spl9_28
  <=> v1_funct_1(u1_lattices(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f230,plain,
    ( v1_funct_1(u1_lattices(sK8))
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f179,f105])).

fof(f239,plain,
    ( spl9_26
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f227,f171,f237])).

fof(f237,plain,
    ( spl9_26
  <=> v1_funct_1(u2_lattices(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f227,plain,
    ( v1_funct_1(u2_lattices(sK7))
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f172,f102])).

fof(f226,plain,
    ( spl9_24
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f198,f164,f224])).

fof(f164,plain,
    ( spl9_8
  <=> l3_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f198,plain,
    ( l2_lattices(sK6)
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f165,f101])).

fof(f101,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',dt_l3_lattices)).

fof(f165,plain,
    ( l3_lattices(sK6)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f219,plain,
    ( spl9_22
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f196,f164,f217])).

fof(f196,plain,
    ( l1_lattices(sK6)
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f165,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f212,plain,
    ( spl9_20
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f197,f157,f210])).

fof(f197,plain,
    ( l2_lattices(sK0)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f158,f101])).

fof(f205,plain,
    ( spl9_18
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f195,f157,f203])).

fof(f195,plain,
    ( l1_lattices(sK0)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f158,f100])).

fof(f194,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f97,f192])).

fof(f97,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f77])).

fof(f187,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f96,f185])).

fof(f96,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f77])).

fof(f180,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f131,f178])).

fof(f131,plain,(
    l1_lattices(sK8) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    l1_lattices(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f23,f90])).

fof(f90,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK8) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',existence_l1_lattices)).

fof(f173,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f130,f171])).

fof(f130,plain,(
    l2_lattices(sK7) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    l2_lattices(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f25,f88])).

fof(f88,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK7) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',existence_l2_lattices)).

fof(f166,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f129,f164])).

fof(f129,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    l3_lattices(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f26,f86])).

fof(f86,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK6) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t23_lattices.p',existence_l3_lattices)).

fof(f159,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f95,f157])).

fof(f95,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f152,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f94,f150])).

fof(f94,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f145,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f93,f143])).

fof(f93,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f138,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f92,f136])).

fof(f92,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).
%------------------------------------------------------------------------------
