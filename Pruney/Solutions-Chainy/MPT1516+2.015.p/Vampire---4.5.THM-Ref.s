%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:50 EST 2020

% Result     : Theorem 3.38s
% Output     : Refutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  307 ( 619 expanded)
%              Number of leaves         :   60 ( 254 expanded)
%              Depth                    :   16
%              Number of atoms          : 1514 (2530 expanded)
%              Number of equality atoms :  261 ( 373 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4511,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f165,f170,f175,f191,f197,f205,f266,f271,f285,f380,f388,f469,f507,f539,f570,f580,f770,f1117,f1122,f1164,f1200,f1284,f1395,f1431,f1449,f1458,f1468,f1609,f1708,f1930,f2711,f4056,f4309,f4364,f4510])).

fof(f4510,plain,
    ( spl12_1
    | spl12_5
    | ~ spl12_10
    | ~ spl12_29
    | ~ spl12_152
    | ~ spl12_224 ),
    inference(avatar_contradiction_clause,[],[f4509])).

fof(f4509,plain,
    ( $false
    | spl12_1
    | spl12_5
    | ~ spl12_10
    | ~ spl12_29
    | ~ spl12_152
    | ~ spl12_224 ),
    inference(subsumption_resolution,[],[f4508,f159])).

fof(f159,plain,
    ( ~ v2_struct_0(sK0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl12_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f4508,plain,
    ( v2_struct_0(sK0)
    | spl12_5
    | ~ spl12_10
    | ~ spl12_29
    | ~ spl12_152
    | ~ spl12_224 ),
    inference(subsumption_resolution,[],[f4507,f260])).

fof(f260,plain,
    ( l1_lattices(sK0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl12_10
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f4507,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl12_5
    | ~ spl12_29
    | ~ spl12_152
    | ~ spl12_224 ),
    inference(subsumption_resolution,[],[f4506,f455])).

fof(f455,plain,
    ( m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl12_29
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f4506,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl12_5
    | ~ spl12_152
    | ~ spl12_224 ),
    inference(subsumption_resolution,[],[f4505,f2710])).

fof(f2710,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))
    | ~ spl12_152 ),
    inference(avatar_component_clause,[],[f2709])).

fof(f2709,plain,
    ( spl12_152
  <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_152])])).

fof(f4505,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl12_5
    | ~ spl12_224 ),
    inference(subsumption_resolution,[],[f4503,f186])).

fof(f186,plain,
    ( ~ v13_lattices(sK0)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl12_5
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f4503,plain,
    ( v13_lattices(sK0)
    | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_224 ),
    inference(trivial_inequality_removal,[],[f4502])).

fof(f4502,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | v13_lattices(sK0)
    | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_224 ),
    inference(superposition,[],[f112,f4363])).

fof(f4363,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl12_224 ),
    inference(avatar_component_clause,[],[f4362])).

fof(f4362,plain,
    ( spl12_224
  <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_224])])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK2(X0,X1),X1) != X1
      | v13_lattices(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f4364,plain,
    ( spl12_224
    | ~ spl12_90
    | ~ spl12_219 ),
    inference(avatar_split_clause,[],[f4314,f4255,f1447,f4362])).

fof(f1447,plain,
    ( spl12_90
  <=> ! [X2] : sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_90])])).

fof(f4255,plain,
    ( spl12_219
  <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_219])])).

fof(f4314,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl12_90
    | ~ spl12_219 ),
    inference(superposition,[],[f4256,f1448])).

fof(f1448,plain,
    ( ! [X2] : sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2))))
    | ~ spl12_90 ),
    inference(avatar_component_clause,[],[f1447])).

fof(f4256,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl12_219 ),
    inference(avatar_component_clause,[],[f4255])).

fof(f4309,plain,
    ( spl12_219
    | ~ spl12_114
    | ~ spl12_211 ),
    inference(avatar_split_clause,[],[f4253,f4054,f1928,f4255])).

fof(f1928,plain,
    ( spl12_114
  <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_114])])).

fof(f4054,plain,
    ( spl12_211
  <=> ! [X16,X17] : k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_211])])).

fof(f4253,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))
    | ~ spl12_114
    | ~ spl12_211 ),
    inference(superposition,[],[f1929,f4055])).

fof(f4055,plain,
    ( ! [X17,X16] : k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16))
    | ~ spl12_211 ),
    inference(avatar_component_clause,[],[f4054])).

fof(f1929,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1))
    | ~ spl12_114 ),
    inference(avatar_component_clause,[],[f1928])).

fof(f4056,plain,
    ( spl12_211
    | spl12_1
    | ~ spl12_4
    | ~ spl12_105 ),
    inference(avatar_split_clause,[],[f1794,f1706,f172,f157,f4054])).

fof(f172,plain,
    ( spl12_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f1706,plain,
    ( spl12_105
  <=> ! [X7,X8] :
        ( k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_105])])).

fof(f1794,plain,
    ( ! [X17,X16] : k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f1793,f159])).

fof(f1793,plain,
    ( ! [X17,X16] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16))
        | v2_struct_0(sK0) )
    | ~ spl12_4
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f1783,f174])).

fof(f174,plain,
    ( l3_lattices(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1783,plain,
    ( ! [X17,X16] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_105 ),
    inference(resolution,[],[f1707,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f1707,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7) )
    | ~ spl12_105 ),
    inference(avatar_component_clause,[],[f1706])).

fof(f2711,plain,
    ( spl12_152
    | ~ spl12_90
    | ~ spl12_114 ),
    inference(avatar_split_clause,[],[f1946,f1928,f1447,f2709])).

fof(f1946,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))
    | ~ spl12_90
    | ~ spl12_114 ),
    inference(superposition,[],[f1929,f1448])).

fof(f1930,plain,
    ( spl12_114
    | ~ spl12_29
    | ~ spl12_70
    | ~ spl12_93 ),
    inference(avatar_split_clause,[],[f1564,f1466,f1282,f454,f1928])).

fof(f1282,plain,
    ( spl12_70
  <=> ! [X2] : k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).

fof(f1466,plain,
    ( spl12_93
  <=> ! [X7,X8] :
        ( k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_93])])).

fof(f1564,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1))
    | ~ spl12_29
    | ~ spl12_70
    | ~ spl12_93 ),
    inference(forward_demodulation,[],[f1551,f1283])).

fof(f1283,plain,
    ( ! [X2] : k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))
    | ~ spl12_70 ),
    inference(avatar_component_clause,[],[f1282])).

fof(f1551,plain,
    ( ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1)))
    | ~ spl12_29
    | ~ spl12_93 ),
    inference(resolution,[],[f1467,f455])).

fof(f1467,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7 )
    | ~ spl12_93 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1708,plain,
    ( spl12_105
    | spl12_1
    | ~ spl12_4
    | ~ spl12_35 ),
    inference(avatar_split_clause,[],[f1030,f568,f172,f157,f1706])).

fof(f568,plain,
    ( spl12_35
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).

fof(f1030,plain,
    ( ! [X8,X7] :
        ( k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | spl12_1
    | ~ spl12_4
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f1029,f159])).

fof(f1029,plain,
    ( ! [X8,X7] :
        ( k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl12_4
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f1019,f174])).

fof(f1019,plain,
    ( ! [X8,X7] :
        ( k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_35 ),
    inference(resolution,[],[f569,f136])).

fof(f569,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl12_35 ),
    inference(avatar_component_clause,[],[f568])).

fof(f1609,plain,
    ( spl12_1
    | ~ spl12_4
    | spl12_6
    | ~ spl12_44
    | ~ spl12_86
    | ~ spl12_92 ),
    inference(avatar_contradiction_clause,[],[f1608])).

fof(f1608,plain,
    ( $false
    | spl12_1
    | ~ spl12_4
    | spl12_6
    | ~ spl12_44
    | ~ spl12_86
    | ~ spl12_92 ),
    inference(subsumption_resolution,[],[f1606,f190])).

fof(f190,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl12_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl12_6
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f1606,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl12_1
    | ~ spl12_4
    | ~ spl12_44
    | ~ spl12_86
    | ~ spl12_92 ),
    inference(backward_demodulation,[],[f1430,f1530])).

fof(f1530,plain,
    ( ! [X2] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_44
    | ~ spl12_92 ),
    inference(forward_demodulation,[],[f1529,f769])).

fof(f769,plain,
    ( ! [X2] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2))
    | ~ spl12_44 ),
    inference(avatar_component_clause,[],[f768])).

fof(f768,plain,
    ( spl12_44
  <=> ! [X2] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f1529,plain,
    ( ! [X2] : k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_92 ),
    inference(subsumption_resolution,[],[f1528,f159])).

fof(f1528,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
        | v2_struct_0(sK0) )
    | ~ spl12_4
    | ~ spl12_92 ),
    inference(subsumption_resolution,[],[f1516,f174])).

fof(f1516,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_92 ),
    inference(resolution,[],[f1457,f136])).

fof(f1457,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6) )
    | ~ spl12_92 ),
    inference(avatar_component_clause,[],[f1456])).

fof(f1456,plain,
    ( spl12_92
  <=> ! [X6] :
        ( k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_92])])).

fof(f1430,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl12_86 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f1428,plain,
    ( spl12_86
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).

fof(f1468,plain,
    ( spl12_93
    | spl12_1
    | ~ spl12_4
    | ~ spl12_37 ),
    inference(avatar_split_clause,[],[f1053,f578,f172,f157,f1466])).

fof(f578,plain,
    ( spl12_37
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f1053,plain,
    ( ! [X8,X7] :
        ( k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | spl12_1
    | ~ spl12_4
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f1052,f159])).

fof(f1052,plain,
    ( ! [X8,X7] :
        ( k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl12_4
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f1042,f174])).

fof(f1042,plain,
    ( ! [X8,X7] :
        ( k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_37 ),
    inference(resolution,[],[f579,f136])).

fof(f579,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl12_37 ),
    inference(avatar_component_clause,[],[f578])).

fof(f1458,plain,
    ( spl12_92
    | spl12_1
    | ~ spl12_10
    | ~ spl12_35 ),
    inference(avatar_split_clause,[],[f1028,f568,f259,f157,f1456])).

fof(f1028,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | spl12_1
    | ~ spl12_10
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f1027,f159])).

fof(f1027,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl12_10
    | ~ spl12_35 ),
    inference(subsumption_resolution,[],[f1018,f260])).

fof(f1018,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_35 ),
    inference(resolution,[],[f569,f103])).

fof(f103,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f1449,plain,
    ( spl12_90
    | spl12_1
    | ~ spl12_4
    | ~ spl12_32 ),
    inference(avatar_split_clause,[],[f973,f505,f172,f157,f1447])).

fof(f505,plain,
    ( spl12_32
  <=> ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f973,plain,
    ( ! [X2] : sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2))))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f972,f159])).

fof(f972,plain,
    ( ! [X2] :
        ( sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2))))
        | v2_struct_0(sK0) )
    | ~ spl12_4
    | ~ spl12_32 ),
    inference(subsumption_resolution,[],[f962,f174])).

fof(f962,plain,
    ( ! [X2] :
        ( sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2))))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_32 ),
    inference(resolution,[],[f506,f136])).

fof(f506,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) )
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f505])).

fof(f1431,plain,
    ( spl12_86
    | ~ spl12_29
    | ~ spl12_65
    | ~ spl12_84 ),
    inference(avatar_split_clause,[],[f1413,f1393,f1197,f454,f1428])).

fof(f1197,plain,
    ( spl12_65
  <=> k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_65])])).

fof(f1393,plain,
    ( spl12_84
  <=> ! [X6] :
        ( k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_84])])).

fof(f1413,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl12_29
    | ~ spl12_65
    | ~ spl12_84 ),
    inference(forward_demodulation,[],[f1401,f1199])).

fof(f1199,plain,
    ( k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl12_65 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f1401,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)))
    | ~ spl12_29
    | ~ spl12_84 ),
    inference(resolution,[],[f1394,f455])).

fof(f1394,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6 )
    | ~ spl12_84 ),
    inference(avatar_component_clause,[],[f1393])).

fof(f1395,plain,
    ( spl12_84
    | spl12_1
    | ~ spl12_10
    | ~ spl12_37 ),
    inference(avatar_split_clause,[],[f1051,f578,f259,f157,f1393])).

fof(f1051,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | spl12_1
    | ~ spl12_10
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f1050,f159])).

fof(f1050,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl12_10
    | ~ spl12_37 ),
    inference(subsumption_resolution,[],[f1041,f260])).

fof(f1041,plain,
    ( ! [X6] :
        ( k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_37 ),
    inference(resolution,[],[f579,f103])).

fof(f1284,plain,
    ( spl12_70
    | spl12_1
    | ~ spl12_4
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f1186,f1162,f172,f157,f1282])).

fof(f1162,plain,
    ( spl12_62
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f1186,plain,
    ( ! [X2] : k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_62 ),
    inference(subsumption_resolution,[],[f1185,f159])).

fof(f1185,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))
        | v2_struct_0(sK0) )
    | ~ spl12_4
    | ~ spl12_62 ),
    inference(subsumption_resolution,[],[f1175,f174])).

fof(f1175,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_62 ),
    inference(resolution,[],[f1163,f136])).

fof(f1163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 )
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1200,plain,
    ( spl12_65
    | ~ spl12_12
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f1169,f1162,f282,f1197])).

fof(f282,plain,
    ( spl12_12
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f1169,plain,
    ( k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl12_12
    | ~ spl12_62 ),
    inference(resolution,[],[f1163,f284])).

fof(f284,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f282])).

fof(f1164,plain,
    ( spl12_62
    | ~ spl12_22
    | ~ spl12_29
    | ~ spl12_59 ),
    inference(avatar_split_clause,[],[f1133,f1115,f454,f378,f1162])).

fof(f378,plain,
    ( spl12_22
  <=> ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r4_lattice3(sK0,X8,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f1115,plain,
    ( spl12_59
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ r4_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f1133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 )
    | ~ spl12_22
    | ~ spl12_29
    | ~ spl12_59 ),
    inference(subsumption_resolution,[],[f1128,f379])).

fof(f379,plain,
    ( ! [X8] :
        ( r4_lattice3(sK0,X8,k1_xboole_0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1128,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0
        | ~ r4_lattice3(sK0,X0,k1_xboole_0) )
    | ~ spl12_29
    | ~ spl12_59 ),
    inference(resolution,[],[f1116,f455])).

fof(f1116,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ r4_lattice3(sK0,X0,X1) )
    | ~ spl12_59 ),
    inference(avatar_component_clause,[],[f1115])).

fof(f1122,plain,
    ( ~ spl12_4
    | spl12_58 ),
    inference(avatar_contradiction_clause,[],[f1121])).

fof(f1121,plain,
    ( $false
    | ~ spl12_4
    | spl12_58 ),
    inference(subsumption_resolution,[],[f1119,f174])).

fof(f1119,plain,
    ( ~ l3_lattices(sK0)
    | spl12_58 ),
    inference(resolution,[],[f1113,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f1113,plain,
    ( ~ l2_lattices(sK0)
    | spl12_58 ),
    inference(avatar_component_clause,[],[f1111])).

fof(f1111,plain,
    ( spl12_58
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).

fof(f1117,plain,
    ( ~ spl12_58
    | spl12_59
    | spl12_1
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f413,f386,f157,f1115,f1111])).

fof(f386,plain,
    ( spl12_24
  <=> ! [X1,X0] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f413,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0) )
    | spl12_1
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f412,f159])).

fof(f412,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_24 ),
    inference(duplicate_literal_removal,[],[f408])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1)
        | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_24 ),
    inference(resolution,[],[f387,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f387,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r4_lattice3(sK0,X0,X1) )
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f386])).

fof(f770,plain,
    ( spl12_44
    | spl12_1
    | ~ spl12_4
    | ~ spl12_33 ),
    inference(avatar_split_clause,[],[f753,f537,f172,f157,f768])).

fof(f537,plain,
    ( spl12_33
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f753,plain,
    ( ! [X2] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f752,f159])).

fof(f752,plain,
    ( ! [X2] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2))
        | v2_struct_0(sK0) )
    | ~ spl12_4
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f742,f174])).

fof(f742,plain,
    ( ! [X2] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_33 ),
    inference(resolution,[],[f538,f136])).

fof(f538,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) )
    | ~ spl12_33 ),
    inference(avatar_component_clause,[],[f537])).

fof(f580,plain,
    ( spl12_37
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f477,f172,f162,f157,f578])).

fof(f162,plain,
    ( spl12_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f477,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f476,f159])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f475,f174])).

fof(f475,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f310,f164])).

fof(f164,plain,
    ( v10_lattices(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f162])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f127,f100])).

fof(f100,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f127,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0)))
            & m1_subset_1(sK9(X0),u1_struct_0(X0))
            & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f73,f75,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0)))
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
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
    inference(rectify,[],[f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(f570,plain,
    ( spl12_35
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f472,f172,f162,f157,f568])).

fof(f472,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f471,f174])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0) )
    | spl12_1
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f470,f159])).

fof(f470,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0) )
    | ~ spl12_2 ),
    inference(resolution,[],[f299,f164])).

fof(f299,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f298,f92])).

fof(f92,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f298,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f113,f97])).

fof(f97,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    ! [X4,X0,X3] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f539,plain,
    ( spl12_33
    | spl12_1
    | ~ spl12_5
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f525,f259,f184,f157,f537])).

fof(f525,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) )
    | spl12_1
    | ~ spl12_5
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f524,f159])).

fof(f524,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)
        | v2_struct_0(sK0) )
    | ~ spl12_5
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f517,f260])).

fof(f517,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_5 ),
    inference(resolution,[],[f185,f328])).

fof(f328,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f145,f103])).

fof(f145,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f185,plain,
    ( v13_lattices(sK0)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f184])).

fof(f507,plain,
    ( spl12_32
    | spl12_1
    | spl12_5
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f498,f259,f203,f184,f157,f505])).

fof(f203,plain,
    ( spl12_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f498,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl12_1
    | spl12_5
    | ~ spl12_8
    | ~ spl12_10 ),
    inference(subsumption_resolution,[],[f222,f260])).

fof(f222,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0) )
    | spl12_1
    | spl12_5
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f221,f159])).

fof(f221,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl12_5
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f212,f186])).

fof(f212,plain,
    ( ! [X1] :
        ( sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_8 ),
    inference(resolution,[],[f204,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 )
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f203])).

fof(f469,plain,
    ( spl12_1
    | ~ spl12_4
    | spl12_29 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl12_1
    | ~ spl12_4
    | spl12_29 ),
    inference(subsumption_resolution,[],[f467,f159])).

fof(f467,plain,
    ( v2_struct_0(sK0)
    | ~ spl12_4
    | spl12_29 ),
    inference(subsumption_resolution,[],[f465,f174])).

fof(f465,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl12_29 ),
    inference(resolution,[],[f456,f136])).

fof(f456,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl12_29 ),
    inference(avatar_component_clause,[],[f454])).

fof(f388,plain,
    ( spl12_24
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f351,f172,f167,f162,f157,f386])).

fof(f167,plain,
    ( spl12_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) )
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f350,f159])).

fof(f350,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f349,f164])).

fof(f349,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f348,f174])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( ~ r4_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_3 ),
    inference(resolution,[],[f345,f169])).

fof(f169,plain,
    ( v4_lattice3(sK0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f167])).

fof(f345,plain,(
    ! [X4,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f152,f136])).

fof(f152,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
                & r4_lattice3(X0,sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f69,f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK7(X0,X1,X2))
        & r4_lattice3(X0,sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f380,plain,
    ( spl12_22
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f373,f195,f378])).

fof(f195,plain,
    ( spl12_7
  <=> ! [X1,X0] :
        ( r2_hidden(sK10(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f373,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r4_lattice3(sK0,X8,k1_xboole_0) )
    | ~ spl12_7 ),
    inference(resolution,[],[f196,f176])).

fof(f176,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f135,f148])).

fof(f148,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f135,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f196,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK10(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f195])).

fof(f285,plain,
    ( spl12_12
    | spl12_1
    | ~ spl12_4
    | ~ spl12_11 ),
    inference(avatar_split_clause,[],[f280,f263,f172,f157,f282])).

fof(f263,plain,
    ( spl12_11
  <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f280,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f279,f159])).

fof(f279,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_11 ),
    inference(subsumption_resolution,[],[f274,f174])).

fof(f274,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_11 ),
    inference(superposition,[],[f136,f265])).

fof(f265,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f263])).

fof(f271,plain,
    ( ~ spl12_4
    | spl12_10 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl12_4
    | spl12_10 ),
    inference(subsumption_resolution,[],[f268,f174])).

fof(f268,plain,
    ( ~ l3_lattices(sK0)
    | spl12_10 ),
    inference(resolution,[],[f261,f92])).

fof(f261,plain,
    ( ~ l1_lattices(sK0)
    | spl12_10 ),
    inference(avatar_component_clause,[],[f259])).

fof(f266,plain,
    ( ~ spl12_10
    | spl12_11
    | spl12_1
    | ~ spl12_8 ),
    inference(avatar_split_clause,[],[f218,f203,f157,f263,f259])).

fof(f218,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | spl12_1
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f210,f159])).

fof(f210,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_8 ),
    inference(resolution,[],[f204,f103])).

fof(f205,plain,
    ( spl12_8
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f201,f172,f167,f162,f157,f203])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 )
    | spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f200,f159])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | v2_struct_0(sK0) )
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f199,f164])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f198,f174])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl12_3 ),
    inference(resolution,[],[f117,f169])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(f197,plain,
    ( spl12_7
    | spl12_1
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f193,f172,f157,f195])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK10(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1) )
    | spl12_1
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f192,f159])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK10(sK0,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r4_lattice3(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl12_4 ),
    inference(resolution,[],[f133,f174])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | r2_hidden(sK10(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK10(X0,X1,X2),X1)
                  & r2_hidden(sK10(X0,X1,X2),X2)
                  & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK10(X0,X1,X2),X1)
        & r2_hidden(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f191,plain,
    ( ~ spl12_5
    | ~ spl12_6
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f182,f172,f162,f157,f188,f184])).

fof(f182,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f181,f159])).

fof(f181,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f180,f164])).

fof(f180,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f91,f174])).

fof(f91,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f175,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f90,f172])).

fof(f90,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f170,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f89,f167])).

fof(f89,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f165,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f88,f162])).

fof(f88,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f160,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f87,f157])).

fof(f87,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (13334)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (13342)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (13323)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (13323)Refutation not found, incomplete strategy% (13323)------------------------------
% 0.21/0.50  % (13323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13323)Memory used [KB]: 10618
% 0.21/0.50  % (13323)Time elapsed: 0.083 s
% 0.21/0.50  % (13323)------------------------------
% 0.21/0.50  % (13323)------------------------------
% 0.21/0.50  % (13339)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (13344)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (13340)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (13336)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (13327)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (13329)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (13338)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (13328)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (13330)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (13322)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (13328)Refutation not found, incomplete strategy% (13328)------------------------------
% 0.21/0.52  % (13328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13328)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13328)Memory used [KB]: 10618
% 0.21/0.52  % (13328)Time elapsed: 0.004 s
% 0.21/0.52  % (13328)------------------------------
% 0.21/0.52  % (13328)------------------------------
% 0.21/0.52  % (13333)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (13335)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (13333)Refutation not found, incomplete strategy% (13333)------------------------------
% 0.21/0.52  % (13333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13333)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13333)Memory used [KB]: 10490
% 0.21/0.52  % (13333)Time elapsed: 0.002 s
% 0.21/0.52  % (13333)------------------------------
% 0.21/0.52  % (13333)------------------------------
% 0.21/0.52  % (13335)Refutation not found, incomplete strategy% (13335)------------------------------
% 0.21/0.52  % (13335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13335)Memory used [KB]: 6140
% 0.21/0.52  % (13335)Time elapsed: 0.108 s
% 0.21/0.52  % (13335)------------------------------
% 0.21/0.52  % (13335)------------------------------
% 0.21/0.52  % (13346)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (13329)Refutation not found, incomplete strategy% (13329)------------------------------
% 0.21/0.53  % (13329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13329)Memory used [KB]: 1791
% 0.21/0.53  % (13329)Time elapsed: 0.109 s
% 0.21/0.53  % (13329)------------------------------
% 0.21/0.53  % (13329)------------------------------
% 0.21/0.53  % (13326)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (13347)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (13324)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (13343)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (13325)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (13322)Refutation not found, incomplete strategy% (13322)------------------------------
% 0.21/0.54  % (13322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13322)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13322)Memory used [KB]: 10618
% 0.21/0.54  % (13322)Time elapsed: 0.098 s
% 0.21/0.54  % (13322)------------------------------
% 0.21/0.54  % (13322)------------------------------
% 0.21/0.54  % (13341)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (13345)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (13331)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (13337)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (13332)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 2.16/0.65  % (13331)Refutation not found, incomplete strategy% (13331)------------------------------
% 2.16/0.65  % (13331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.65  % (13331)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.65  
% 2.16/0.65  % (13331)Memory used [KB]: 6140
% 2.16/0.65  % (13331)Time elapsed: 0.231 s
% 2.16/0.65  % (13331)------------------------------
% 2.16/0.65  % (13331)------------------------------
% 3.38/0.81  % (13324)Refutation found. Thanks to Tanya!
% 3.38/0.81  % SZS status Theorem for theBenchmark
% 3.38/0.81  % SZS output start Proof for theBenchmark
% 3.38/0.81  fof(f4511,plain,(
% 3.38/0.81    $false),
% 3.38/0.81    inference(avatar_sat_refutation,[],[f160,f165,f170,f175,f191,f197,f205,f266,f271,f285,f380,f388,f469,f507,f539,f570,f580,f770,f1117,f1122,f1164,f1200,f1284,f1395,f1431,f1449,f1458,f1468,f1609,f1708,f1930,f2711,f4056,f4309,f4364,f4510])).
% 3.38/0.81  fof(f4510,plain,(
% 3.38/0.81    spl12_1 | spl12_5 | ~spl12_10 | ~spl12_29 | ~spl12_152 | ~spl12_224),
% 3.38/0.81    inference(avatar_contradiction_clause,[],[f4509])).
% 3.38/0.81  fof(f4509,plain,(
% 3.38/0.81    $false | (spl12_1 | spl12_5 | ~spl12_10 | ~spl12_29 | ~spl12_152 | ~spl12_224)),
% 3.38/0.81    inference(subsumption_resolution,[],[f4508,f159])).
% 3.38/0.81  fof(f159,plain,(
% 3.38/0.81    ~v2_struct_0(sK0) | spl12_1),
% 3.38/0.81    inference(avatar_component_clause,[],[f157])).
% 3.38/0.81  fof(f157,plain,(
% 3.38/0.81    spl12_1 <=> v2_struct_0(sK0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 3.38/0.81  fof(f4508,plain,(
% 3.38/0.81    v2_struct_0(sK0) | (spl12_5 | ~spl12_10 | ~spl12_29 | ~spl12_152 | ~spl12_224)),
% 3.38/0.81    inference(subsumption_resolution,[],[f4507,f260])).
% 3.38/0.81  fof(f260,plain,(
% 3.38/0.81    l1_lattices(sK0) | ~spl12_10),
% 3.38/0.81    inference(avatar_component_clause,[],[f259])).
% 3.38/0.81  fof(f259,plain,(
% 3.38/0.81    spl12_10 <=> l1_lattices(sK0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 3.38/0.81  fof(f4507,plain,(
% 3.38/0.81    ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl12_5 | ~spl12_29 | ~spl12_152 | ~spl12_224)),
% 3.38/0.81    inference(subsumption_resolution,[],[f4506,f455])).
% 3.38/0.81  fof(f455,plain,(
% 3.38/0.81    m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl12_29),
% 3.38/0.81    inference(avatar_component_clause,[],[f454])).
% 3.38/0.81  fof(f454,plain,(
% 3.38/0.81    spl12_29 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).
% 3.38/0.81  fof(f4506,plain,(
% 3.38/0.81    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl12_5 | ~spl12_152 | ~spl12_224)),
% 3.38/0.81    inference(subsumption_resolution,[],[f4505,f2710])).
% 3.38/0.81  fof(f2710,plain,(
% 3.38/0.81    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))) ) | ~spl12_152),
% 3.38/0.81    inference(avatar_component_clause,[],[f2709])).
% 3.38/0.81  fof(f2709,plain,(
% 3.38/0.81    spl12_152 <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_152])])).
% 3.38/0.81  fof(f4505,plain,(
% 3.38/0.81    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (spl12_5 | ~spl12_224)),
% 3.38/0.81    inference(subsumption_resolution,[],[f4503,f186])).
% 3.38/0.81  fof(f186,plain,(
% 3.38/0.81    ~v13_lattices(sK0) | spl12_5),
% 3.38/0.81    inference(avatar_component_clause,[],[f184])).
% 3.38/0.81  fof(f184,plain,(
% 3.38/0.81    spl12_5 <=> v13_lattices(sK0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 3.38/0.81  fof(f4503,plain,(
% 3.38/0.81    v13_lattices(sK0) | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl12_224),
% 3.38/0.81    inference(trivial_inequality_removal,[],[f4502])).
% 3.38/0.81  fof(f4502,plain,(
% 3.38/0.81    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | v13_lattices(sK0) | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl12_224),
% 3.38/0.81    inference(superposition,[],[f112,f4363])).
% 3.38/0.81  fof(f4363,plain,(
% 3.38/0.81    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))) ) | ~spl12_224),
% 3.38/0.81    inference(avatar_component_clause,[],[f4362])).
% 3.38/0.81  fof(f4362,plain,(
% 3.38/0.81    spl12_224 <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_224])])).
% 3.38/0.81  fof(f112,plain,(
% 3.38/0.81    ( ! [X0,X1] : (k2_lattices(X0,sK2(X0,X1),X1) != X1 | v13_lattices(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f59])).
% 3.38/0.81  fof(f59,plain,(
% 3.38/0.81    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).
% 3.38/0.81  fof(f57,plain,(
% 3.38/0.81    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f58,plain,(
% 3.38/0.81    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f56,plain,(
% 3.38/0.81    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(rectify,[],[f55])).
% 3.38/0.81  fof(f55,plain,(
% 3.38/0.81    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(nnf_transformation,[],[f31])).
% 3.38/0.81  fof(f31,plain,(
% 3.38/0.81    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f30])).
% 3.38/0.81  fof(f30,plain,(
% 3.38/0.81    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f9])).
% 3.38/0.81  fof(f9,axiom,(
% 3.38/0.81    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 3.38/0.81  fof(f4364,plain,(
% 3.38/0.81    spl12_224 | ~spl12_90 | ~spl12_219),
% 3.38/0.81    inference(avatar_split_clause,[],[f4314,f4255,f1447,f4362])).
% 3.38/0.81  fof(f1447,plain,(
% 3.38/0.81    spl12_90 <=> ! [X2] : sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2))))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_90])])).
% 3.38/0.81  fof(f4255,plain,(
% 3.38/0.81    spl12_219 <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_219])])).
% 3.38/0.81  fof(f4314,plain,(
% 3.38/0.81    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,k1_xboole_0))) ) | (~spl12_90 | ~spl12_219)),
% 3.38/0.81    inference(superposition,[],[f4256,f1448])).
% 3.38/0.81  fof(f1448,plain,(
% 3.38/0.81    ( ! [X2] : (sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2))))) ) | ~spl12_90),
% 3.38/0.81    inference(avatar_component_clause,[],[f1447])).
% 3.38/0.81  fof(f4256,plain,(
% 3.38/0.81    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))) ) | ~spl12_219),
% 3.38/0.81    inference(avatar_component_clause,[],[f4255])).
% 3.38/0.81  fof(f4309,plain,(
% 3.38/0.81    spl12_219 | ~spl12_114 | ~spl12_211),
% 3.38/0.81    inference(avatar_split_clause,[],[f4253,f4054,f1928,f4255])).
% 3.38/0.81  fof(f1928,plain,(
% 3.38/0.81    spl12_114 <=> ! [X1] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_114])])).
% 3.38/0.81  fof(f4054,plain,(
% 3.38/0.81    spl12_211 <=> ! [X16,X17] : k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_211])])).
% 3.38/0.81  fof(f4253,plain,(
% 3.38/0.81    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))) ) | (~spl12_114 | ~spl12_211)),
% 3.38/0.81    inference(superposition,[],[f1929,f4055])).
% 3.38/0.81  fof(f4055,plain,(
% 3.38/0.81    ( ! [X17,X16] : (k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16))) ) | ~spl12_211),
% 3.38/0.81    inference(avatar_component_clause,[],[f4054])).
% 3.38/0.81  fof(f1929,plain,(
% 3.38/0.81    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1))) ) | ~spl12_114),
% 3.38/0.81    inference(avatar_component_clause,[],[f1928])).
% 3.38/0.81  fof(f4056,plain,(
% 3.38/0.81    spl12_211 | spl12_1 | ~spl12_4 | ~spl12_105),
% 3.38/0.81    inference(avatar_split_clause,[],[f1794,f1706,f172,f157,f4054])).
% 3.38/0.81  fof(f172,plain,(
% 3.38/0.81    spl12_4 <=> l3_lattices(sK0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 3.38/0.81  fof(f1706,plain,(
% 3.38/0.81    spl12_105 <=> ! [X7,X8] : (k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7) | ~m1_subset_1(X7,u1_struct_0(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_105])])).
% 3.38/0.81  fof(f1794,plain,(
% 3.38/0.81    ( ! [X17,X16] : (k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16))) ) | (spl12_1 | ~spl12_4 | ~spl12_105)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1793,f159])).
% 3.38/0.81  fof(f1793,plain,(
% 3.38/0.81    ( ! [X17,X16] : (k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16)) | v2_struct_0(sK0)) ) | (~spl12_4 | ~spl12_105)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1783,f174])).
% 3.38/0.81  fof(f174,plain,(
% 3.38/0.81    l3_lattices(sK0) | ~spl12_4),
% 3.38/0.81    inference(avatar_component_clause,[],[f172])).
% 3.38/0.81  fof(f1783,plain,(
% 3.38/0.81    ( ! [X17,X16] : (k2_lattices(sK0,k15_lattice3(sK0,X16),k15_lattice3(sK0,X17)) = k2_lattices(sK0,k15_lattice3(sK0,X17),k15_lattice3(sK0,X16)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_105),
% 3.38/0.81    inference(resolution,[],[f1707,f136])).
% 3.38/0.81  fof(f136,plain,(
% 3.38/0.81    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f45])).
% 3.38/0.81  fof(f45,plain,(
% 3.38/0.81    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f44])).
% 3.38/0.81  fof(f44,plain,(
% 3.38/0.81    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f13])).
% 3.38/0.81  fof(f13,axiom,(
% 3.38/0.81    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 3.38/0.81  fof(f1707,plain,(
% 3.38/0.81    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7)) ) | ~spl12_105),
% 3.38/0.81    inference(avatar_component_clause,[],[f1706])).
% 3.38/0.81  fof(f2711,plain,(
% 3.38/0.81    spl12_152 | ~spl12_90 | ~spl12_114),
% 3.38/0.81    inference(avatar_split_clause,[],[f1946,f1928,f1447,f2709])).
% 3.38/0.81  fof(f1946,plain,(
% 3.38/0.81    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X1)))) ) | (~spl12_90 | ~spl12_114)),
% 3.38/0.81    inference(superposition,[],[f1929,f1448])).
% 3.38/0.81  fof(f1930,plain,(
% 3.38/0.81    spl12_114 | ~spl12_29 | ~spl12_70 | ~spl12_93),
% 3.38/0.81    inference(avatar_split_clause,[],[f1564,f1466,f1282,f454,f1928])).
% 3.38/0.81  fof(f1282,plain,(
% 3.38/0.81    spl12_70 <=> ! [X2] : k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).
% 3.38/0.81  fof(f1466,plain,(
% 3.38/0.81    spl12_93 <=> ! [X7,X8] : (k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_93])])).
% 3.38/0.81  fof(f1564,plain,(
% 3.38/0.81    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1))) ) | (~spl12_29 | ~spl12_70 | ~spl12_93)),
% 3.38/0.81    inference(forward_demodulation,[],[f1551,f1283])).
% 3.38/0.81  fof(f1283,plain,(
% 3.38/0.81    ( ! [X2] : (k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))) ) | ~spl12_70),
% 3.38/0.81    inference(avatar_component_clause,[],[f1282])).
% 3.38/0.81  fof(f1551,plain,(
% 3.38/0.81    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X1)))) ) | (~spl12_29 | ~spl12_93)),
% 3.38/0.81    inference(resolution,[],[f1467,f455])).
% 3.38/0.81  fof(f1467,plain,(
% 3.38/0.81    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7) ) | ~spl12_93),
% 3.38/0.81    inference(avatar_component_clause,[],[f1466])).
% 3.38/0.81  fof(f1708,plain,(
% 3.38/0.81    spl12_105 | spl12_1 | ~spl12_4 | ~spl12_35),
% 3.38/0.81    inference(avatar_split_clause,[],[f1030,f568,f172,f157,f1706])).
% 3.38/0.81  fof(f568,plain,(
% 3.38/0.81    spl12_35 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).
% 3.38/0.81  fof(f1030,plain,(
% 3.38/0.81    ( ! [X8,X7] : (k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_4 | ~spl12_35)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1029,f159])).
% 3.38/0.81  fof(f1029,plain,(
% 3.38/0.81    ( ! [X8,X7] : (k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl12_4 | ~spl12_35)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1019,f174])).
% 3.38/0.81  fof(f1019,plain,(
% 3.38/0.81    ( ! [X8,X7] : (k2_lattices(sK0,X7,k15_lattice3(sK0,X8)) = k2_lattices(sK0,k15_lattice3(sK0,X8),X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_35),
% 3.38/0.81    inference(resolution,[],[f569,f136])).
% 3.38/0.81  fof(f569,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl12_35),
% 3.38/0.81    inference(avatar_component_clause,[],[f568])).
% 3.38/0.81  fof(f1609,plain,(
% 3.38/0.81    spl12_1 | ~spl12_4 | spl12_6 | ~spl12_44 | ~spl12_86 | ~spl12_92),
% 3.38/0.81    inference(avatar_contradiction_clause,[],[f1608])).
% 3.38/0.81  fof(f1608,plain,(
% 3.38/0.81    $false | (spl12_1 | ~spl12_4 | spl12_6 | ~spl12_44 | ~spl12_86 | ~spl12_92)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1606,f190])).
% 3.38/0.81  fof(f190,plain,(
% 3.38/0.81    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl12_6),
% 3.38/0.81    inference(avatar_component_clause,[],[f188])).
% 3.38/0.81  fof(f188,plain,(
% 3.38/0.81    spl12_6 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 3.38/0.81  fof(f1606,plain,(
% 3.38/0.81    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl12_1 | ~spl12_4 | ~spl12_44 | ~spl12_86 | ~spl12_92)),
% 3.38/0.81    inference(backward_demodulation,[],[f1430,f1530])).
% 3.38/0.81  fof(f1530,plain,(
% 3.38/0.81    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))) ) | (spl12_1 | ~spl12_4 | ~spl12_44 | ~spl12_92)),
% 3.38/0.81    inference(forward_demodulation,[],[f1529,f769])).
% 3.38/0.81  fof(f769,plain,(
% 3.38/0.81    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2))) ) | ~spl12_44),
% 3.38/0.81    inference(avatar_component_clause,[],[f768])).
% 3.38/0.81  fof(f768,plain,(
% 3.38/0.81    spl12_44 <=> ! [X2] : k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).
% 3.38/0.81  fof(f1529,plain,(
% 3.38/0.81    ( ! [X2] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))) ) | (spl12_1 | ~spl12_4 | ~spl12_92)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1528,f159])).
% 3.38/0.81  fof(f1528,plain,(
% 3.38/0.81    ( ! [X2] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | v2_struct_0(sK0)) ) | (~spl12_4 | ~spl12_92)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1516,f174])).
% 3.38/0.81  fof(f1516,plain,(
% 3.38/0.81    ( ! [X2] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_92),
% 3.38/0.81    inference(resolution,[],[f1457,f136])).
% 3.38/0.81  fof(f1457,plain,(
% 3.38/0.81    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6)) ) | ~spl12_92),
% 3.38/0.81    inference(avatar_component_clause,[],[f1456])).
% 3.38/0.81  fof(f1456,plain,(
% 3.38/0.81    spl12_92 <=> ! [X6] : (k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_92])])).
% 3.38/0.81  fof(f1430,plain,(
% 3.38/0.81    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl12_86),
% 3.38/0.81    inference(avatar_component_clause,[],[f1428])).
% 3.38/0.81  fof(f1428,plain,(
% 3.38/0.81    spl12_86 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).
% 3.38/0.81  fof(f1468,plain,(
% 3.38/0.81    spl12_93 | spl12_1 | ~spl12_4 | ~spl12_37),
% 3.38/0.81    inference(avatar_split_clause,[],[f1053,f578,f172,f157,f1466])).
% 3.38/0.81  fof(f578,plain,(
% 3.38/0.81    spl12_37 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).
% 3.38/0.81  fof(f1053,plain,(
% 3.38/0.81    ( ! [X8,X7] : (k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_4 | ~spl12_37)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1052,f159])).
% 3.38/0.81  fof(f1052,plain,(
% 3.38/0.81    ( ! [X8,X7] : (k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl12_4 | ~spl12_37)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1042,f174])).
% 3.38/0.81  fof(f1042,plain,(
% 3.38/0.81    ( ! [X8,X7] : (k2_lattices(sK0,X7,k1_lattices(sK0,X7,k15_lattice3(sK0,X8))) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_37),
% 3.38/0.81    inference(resolution,[],[f579,f136])).
% 3.38/0.81  fof(f579,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl12_37),
% 3.38/0.81    inference(avatar_component_clause,[],[f578])).
% 3.38/0.81  fof(f1458,plain,(
% 3.38/0.81    spl12_92 | spl12_1 | ~spl12_10 | ~spl12_35),
% 3.38/0.81    inference(avatar_split_clause,[],[f1028,f568,f259,f157,f1456])).
% 3.38/0.81  fof(f1028,plain,(
% 3.38/0.81    ( ! [X6] : (k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6) | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_10 | ~spl12_35)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1027,f159])).
% 3.38/0.81  fof(f1027,plain,(
% 3.38/0.81    ( ! [X6] : (k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl12_10 | ~spl12_35)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1018,f260])).
% 3.38/0.81  fof(f1018,plain,(
% 3.38/0.81    ( ! [X6] : (k2_lattices(sK0,X6,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_35),
% 3.38/0.81    inference(resolution,[],[f569,f103])).
% 3.38/0.81  fof(f103,plain,(
% 3.38/0.81    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f27])).
% 3.38/0.81  fof(f27,plain,(
% 3.38/0.81    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f26])).
% 3.38/0.81  fof(f26,plain,(
% 3.38/0.81    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f7])).
% 3.38/0.81  fof(f7,axiom,(
% 3.38/0.81    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 3.38/0.81  fof(f1449,plain,(
% 3.38/0.81    spl12_90 | spl12_1 | ~spl12_4 | ~spl12_32),
% 3.38/0.81    inference(avatar_split_clause,[],[f973,f505,f172,f157,f1447])).
% 3.38/0.81  fof(f505,plain,(
% 3.38/0.81    spl12_32 <=> ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).
% 3.38/0.81  fof(f973,plain,(
% 3.38/0.81    ( ! [X2] : (sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2))))) ) | (spl12_1 | ~spl12_4 | ~spl12_32)),
% 3.38/0.81    inference(subsumption_resolution,[],[f972,f159])).
% 3.38/0.81  fof(f972,plain,(
% 3.38/0.81    ( ! [X2] : (sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2)))) | v2_struct_0(sK0)) ) | (~spl12_4 | ~spl12_32)),
% 3.38/0.81    inference(subsumption_resolution,[],[f962,f174])).
% 3.38/0.81  fof(f962,plain,(
% 3.38/0.81    ( ! [X2] : (sK2(sK0,k15_lattice3(sK0,X2)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X2)))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_32),
% 3.38/0.81    inference(resolution,[],[f506,f136])).
% 3.38/0.81  fof(f506,plain,(
% 3.38/0.81    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1)))) ) | ~spl12_32),
% 3.38/0.81    inference(avatar_component_clause,[],[f505])).
% 3.38/0.81  fof(f1431,plain,(
% 3.38/0.81    spl12_86 | ~spl12_29 | ~spl12_65 | ~spl12_84),
% 3.38/0.81    inference(avatar_split_clause,[],[f1413,f1393,f1197,f454,f1428])).
% 3.38/0.81  fof(f1197,plain,(
% 3.38/0.81    spl12_65 <=> k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_65])])).
% 3.38/0.81  fof(f1393,plain,(
% 3.38/0.81    spl12_84 <=> ! [X6] : (k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_84])])).
% 3.38/0.81  fof(f1413,plain,(
% 3.38/0.81    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl12_29 | ~spl12_65 | ~spl12_84)),
% 3.38/0.81    inference(forward_demodulation,[],[f1401,f1199])).
% 3.38/0.81  fof(f1199,plain,(
% 3.38/0.81    k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl12_65),
% 3.38/0.81    inference(avatar_component_clause,[],[f1197])).
% 3.38/0.81  fof(f1401,plain,(
% 3.38/0.81    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))) | (~spl12_29 | ~spl12_84)),
% 3.38/0.81    inference(resolution,[],[f1394,f455])).
% 3.38/0.81  fof(f1394,plain,(
% 3.38/0.81    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6) ) | ~spl12_84),
% 3.38/0.81    inference(avatar_component_clause,[],[f1393])).
% 3.38/0.81  fof(f1395,plain,(
% 3.38/0.81    spl12_84 | spl12_1 | ~spl12_10 | ~spl12_37),
% 3.38/0.81    inference(avatar_split_clause,[],[f1051,f578,f259,f157,f1393])).
% 3.38/0.81  fof(f1051,plain,(
% 3.38/0.81    ( ! [X6] : (k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_10 | ~spl12_37)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1050,f159])).
% 3.38/0.81  fof(f1050,plain,(
% 3.38/0.81    ( ! [X6] : (k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl12_10 | ~spl12_37)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1041,f260])).
% 3.38/0.81  fof(f1041,plain,(
% 3.38/0.81    ( ! [X6] : (k2_lattices(sK0,X6,k1_lattices(sK0,X6,k5_lattices(sK0))) = X6 | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_37),
% 3.38/0.81    inference(resolution,[],[f579,f103])).
% 3.38/0.81  fof(f1284,plain,(
% 3.38/0.81    spl12_70 | spl12_1 | ~spl12_4 | ~spl12_62),
% 3.38/0.81    inference(avatar_split_clause,[],[f1186,f1162,f172,f157,f1282])).
% 3.38/0.81  fof(f1162,plain,(
% 3.38/0.81    spl12_62 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).
% 3.38/0.81  fof(f1186,plain,(
% 3.38/0.81    ( ! [X2] : (k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2))) ) | (spl12_1 | ~spl12_4 | ~spl12_62)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1185,f159])).
% 3.38/0.81  fof(f1185,plain,(
% 3.38/0.81    ( ! [X2] : (k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2)) | v2_struct_0(sK0)) ) | (~spl12_4 | ~spl12_62)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1175,f174])).
% 3.38/0.81  fof(f1175,plain,(
% 3.38/0.81    ( ! [X2] : (k15_lattice3(sK0,X2) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X2)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_62),
% 3.38/0.81    inference(resolution,[],[f1163,f136])).
% 3.38/0.81  fof(f1163,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0) ) | ~spl12_62),
% 3.38/0.81    inference(avatar_component_clause,[],[f1162])).
% 3.38/0.81  fof(f1200,plain,(
% 3.38/0.81    spl12_65 | ~spl12_12 | ~spl12_62),
% 3.38/0.81    inference(avatar_split_clause,[],[f1169,f1162,f282,f1197])).
% 3.38/0.81  fof(f282,plain,(
% 3.38/0.81    spl12_12 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 3.38/0.81  fof(f1169,plain,(
% 3.38/0.81    k5_lattices(sK0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl12_12 | ~spl12_62)),
% 3.38/0.81    inference(resolution,[],[f1163,f284])).
% 3.38/0.81  fof(f284,plain,(
% 3.38/0.81    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl12_12),
% 3.38/0.81    inference(avatar_component_clause,[],[f282])).
% 3.38/0.81  fof(f1164,plain,(
% 3.38/0.81    spl12_62 | ~spl12_22 | ~spl12_29 | ~spl12_59),
% 3.38/0.81    inference(avatar_split_clause,[],[f1133,f1115,f454,f378,f1162])).
% 3.38/0.81  fof(f378,plain,(
% 3.38/0.81    spl12_22 <=> ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | r4_lattice3(sK0,X8,k1_xboole_0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 3.38/0.81  fof(f1115,plain,(
% 3.38/0.81    spl12_59 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~r4_lattice3(sK0,X0,X1))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).
% 3.38/0.81  fof(f1133,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0) ) | (~spl12_22 | ~spl12_29 | ~spl12_59)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1128,f379])).
% 3.38/0.81  fof(f379,plain,(
% 3.38/0.81    ( ! [X8] : (r4_lattice3(sK0,X8,k1_xboole_0) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | ~spl12_22),
% 3.38/0.81    inference(avatar_component_clause,[],[f378])).
% 3.38/0.81  fof(f1128,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) = X0 | ~r4_lattice3(sK0,X0,k1_xboole_0)) ) | (~spl12_29 | ~spl12_59)),
% 3.38/0.81    inference(resolution,[],[f1116,f455])).
% 3.38/0.81  fof(f1116,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~r4_lattice3(sK0,X0,X1)) ) | ~spl12_59),
% 3.38/0.81    inference(avatar_component_clause,[],[f1115])).
% 3.38/0.81  fof(f1122,plain,(
% 3.38/0.81    ~spl12_4 | spl12_58),
% 3.38/0.81    inference(avatar_contradiction_clause,[],[f1121])).
% 3.38/0.81  fof(f1121,plain,(
% 3.38/0.81    $false | (~spl12_4 | spl12_58)),
% 3.38/0.81    inference(subsumption_resolution,[],[f1119,f174])).
% 3.38/0.81  fof(f1119,plain,(
% 3.38/0.81    ~l3_lattices(sK0) | spl12_58),
% 3.38/0.81    inference(resolution,[],[f1113,f93])).
% 3.38/0.81  fof(f93,plain,(
% 3.38/0.81    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f21])).
% 3.38/0.81  fof(f21,plain,(
% 3.38/0.81    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 3.38/0.81    inference(ennf_transformation,[],[f8])).
% 3.38/0.81  fof(f8,axiom,(
% 3.38/0.81    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 3.38/0.81  fof(f1113,plain,(
% 3.38/0.81    ~l2_lattices(sK0) | spl12_58),
% 3.38/0.81    inference(avatar_component_clause,[],[f1111])).
% 3.38/0.81  fof(f1111,plain,(
% 3.38/0.81    spl12_58 <=> l2_lattices(sK0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_58])])).
% 3.38/0.81  fof(f1117,plain,(
% 3.38/0.81    ~spl12_58 | spl12_59 | spl12_1 | ~spl12_24),
% 3.38/0.81    inference(avatar_split_clause,[],[f413,f386,f157,f1115,f1111])).
% 3.38/0.81  fof(f386,plain,(
% 3.38/0.81    spl12_24 <=> ! [X1,X0] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).
% 3.38/0.81  fof(f413,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0)) ) | (spl12_1 | ~spl12_24)),
% 3.38/0.81    inference(subsumption_resolution,[],[f412,f159])).
% 3.38/0.81  fof(f412,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_24),
% 3.38/0.81    inference(duplicate_literal_removal,[],[f408])).
% 3.38/0.81  fof(f408,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1) | k1_lattices(sK0,k15_lattice3(sK0,X1),X0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_24),
% 3.38/0.81    inference(resolution,[],[f387,f101])).
% 3.38/0.81  fof(f101,plain,(
% 3.38/0.81    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f50])).
% 3.38/0.81  fof(f50,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(nnf_transformation,[],[f25])).
% 3.38/0.81  fof(f25,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f24])).
% 3.38/0.81  fof(f24,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f5])).
% 3.38/0.81  fof(f5,axiom,(
% 3.38/0.81    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 3.38/0.81  fof(f387,plain,(
% 3.38/0.81    ( ! [X0,X1] : (r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r4_lattice3(sK0,X0,X1)) ) | ~spl12_24),
% 3.38/0.81    inference(avatar_component_clause,[],[f386])).
% 3.38/0.81  fof(f770,plain,(
% 3.38/0.81    spl12_44 | spl12_1 | ~spl12_4 | ~spl12_33),
% 3.38/0.81    inference(avatar_split_clause,[],[f753,f537,f172,f157,f768])).
% 3.38/0.81  fof(f537,plain,(
% 3.38/0.81    spl12_33 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).
% 3.38/0.81  fof(f753,plain,(
% 3.38/0.81    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2))) ) | (spl12_1 | ~spl12_4 | ~spl12_33)),
% 3.38/0.81    inference(subsumption_resolution,[],[f752,f159])).
% 3.38/0.81  fof(f752,plain,(
% 3.38/0.81    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) | v2_struct_0(sK0)) ) | (~spl12_4 | ~spl12_33)),
% 3.38/0.81    inference(subsumption_resolution,[],[f742,f174])).
% 3.38/0.81  fof(f742,plain,(
% 3.38/0.81    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X2)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_33),
% 3.38/0.81    inference(resolution,[],[f538,f136])).
% 3.38/0.81  fof(f538,plain,(
% 3.38/0.81    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)) ) | ~spl12_33),
% 3.38/0.81    inference(avatar_component_clause,[],[f537])).
% 3.38/0.81  fof(f580,plain,(
% 3.38/0.81    spl12_37 | spl12_1 | ~spl12_2 | ~spl12_4),
% 3.38/0.81    inference(avatar_split_clause,[],[f477,f172,f162,f157,f578])).
% 3.38/0.81  fof(f162,plain,(
% 3.38/0.81    spl12_2 <=> v10_lattices(sK0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 3.38/0.81  fof(f477,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_2 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f476,f159])).
% 3.38/0.81  fof(f476,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl12_2 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f475,f174])).
% 3.38/0.81  fof(f475,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,X1)) = X0 | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl12_2),
% 3.38/0.81    inference(resolution,[],[f310,f164])).
% 3.38/0.81  fof(f164,plain,(
% 3.38/0.81    v10_lattices(sK0) | ~spl12_2),
% 3.38/0.81    inference(avatar_component_clause,[],[f162])).
% 3.38/0.81  fof(f310,plain,(
% 3.38/0.81    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 | ~l3_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 3.38/0.81    inference(duplicate_literal_removal,[],[f309])).
% 3.38/0.81  fof(f309,plain,(
% 3.38/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X2,k1_lattices(X1,X2,X0)) = X2 | ~l3_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 3.38/0.81    inference(resolution,[],[f127,f100])).
% 3.38/0.81  fof(f100,plain,(
% 3.38/0.81    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f23])).
% 3.38/0.81  fof(f23,plain,(
% 3.38/0.81    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 3.38/0.81    inference(flattening,[],[f22])).
% 3.38/0.81  fof(f22,plain,(
% 3.38/0.81    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 3.38/0.81    inference(ennf_transformation,[],[f3])).
% 3.38/0.81  fof(f3,axiom,(
% 3.38/0.81    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 3.38/0.81  fof(f127,plain,(
% 3.38/0.81    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f76])).
% 3.38/0.81  fof(f76,plain,(
% 3.38/0.81    ! [X0] : (((v9_lattices(X0) | ((sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f73,f75,f74])).
% 3.38/0.81  fof(f74,plain,(
% 3.38/0.81    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f75,plain,(
% 3.38/0.81    ! [X0] : (? [X2] : (sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK8(X0) != k2_lattices(X0,sK8(X0),k1_lattices(X0,sK8(X0),sK9(X0))) & m1_subset_1(sK9(X0),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f73,plain,(
% 3.38/0.81    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(rectify,[],[f72])).
% 3.38/0.81  fof(f72,plain,(
% 3.38/0.81    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(nnf_transformation,[],[f41])).
% 3.38/0.81  fof(f41,plain,(
% 3.38/0.81    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f40])).
% 3.38/0.81  fof(f40,plain,(
% 3.38/0.81    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f6])).
% 3.38/0.81  fof(f6,axiom,(
% 3.38/0.81    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).
% 3.38/0.81  fof(f570,plain,(
% 3.38/0.81    spl12_35 | spl12_1 | ~spl12_2 | ~spl12_4),
% 3.38/0.81    inference(avatar_split_clause,[],[f472,f172,f162,f157,f568])).
% 3.38/0.81  fof(f472,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_2 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f471,f174])).
% 3.38/0.81  fof(f471,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) ) | (spl12_1 | ~spl12_2)),
% 3.38/0.81    inference(subsumption_resolution,[],[f470,f159])).
% 3.38/0.81  fof(f470,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = k2_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) ) | ~spl12_2),
% 3.38/0.81    inference(resolution,[],[f299,f164])).
% 3.38/0.81  fof(f299,plain,(
% 3.38/0.81    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1)) )),
% 3.38/0.81    inference(subsumption_resolution,[],[f298,f92])).
% 3.38/0.81  fof(f92,plain,(
% 3.38/0.81    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f21])).
% 3.38/0.81  fof(f298,plain,(
% 3.38/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~l3_lattices(X1)) )),
% 3.38/0.81    inference(duplicate_literal_removal,[],[f297])).
% 3.38/0.81  fof(f297,plain,(
% 3.38/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | ~l1_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 3.38/0.81    inference(resolution,[],[f113,f97])).
% 3.38/0.81  fof(f97,plain,(
% 3.38/0.81    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f23])).
% 3.38/0.81  fof(f113,plain,(
% 3.38/0.81    ( ! [X4,X0,X3] : (~v6_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f64])).
% 3.38/0.81  fof(f64,plain,(
% 3.38/0.81    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f61,f63,f62])).
% 3.38/0.81  fof(f62,plain,(
% 3.38/0.81    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f63,plain,(
% 3.38/0.81    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f61,plain,(
% 3.38/0.81    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(rectify,[],[f60])).
% 3.38/0.81  fof(f60,plain,(
% 3.38/0.81    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(nnf_transformation,[],[f33])).
% 3.38/0.81  fof(f33,plain,(
% 3.38/0.81    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f32])).
% 3.38/0.81  fof(f32,plain,(
% 3.38/0.81    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f12])).
% 3.38/0.81  fof(f12,axiom,(
% 3.38/0.81    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 3.38/0.81  fof(f539,plain,(
% 3.38/0.81    spl12_33 | spl12_1 | ~spl12_5 | ~spl12_10),
% 3.38/0.81    inference(avatar_split_clause,[],[f525,f259,f184,f157,f537])).
% 3.38/0.81  fof(f525,plain,(
% 3.38/0.81    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1)) ) | (spl12_1 | ~spl12_5 | ~spl12_10)),
% 3.38/0.81    inference(subsumption_resolution,[],[f524,f159])).
% 3.38/0.81  fof(f524,plain,(
% 3.38/0.81    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) | v2_struct_0(sK0)) ) | (~spl12_5 | ~spl12_10)),
% 3.38/0.81    inference(subsumption_resolution,[],[f517,f260])).
% 3.38/0.81  fof(f517,plain,(
% 3.38/0.81    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X1) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_5),
% 3.38/0.81    inference(resolution,[],[f185,f328])).
% 3.38/0.81  fof(f328,plain,(
% 3.38/0.81    ( ! [X0,X3] : (~v13_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(subsumption_resolution,[],[f145,f103])).
% 3.38/0.81  fof(f145,plain,(
% 3.38/0.81    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(equality_resolution,[],[f104])).
% 3.38/0.81  fof(f104,plain,(
% 3.38/0.81    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f54])).
% 3.38/0.81  fof(f54,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f52,f53])).
% 3.38/0.81  fof(f53,plain,(
% 3.38/0.81    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f52,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(rectify,[],[f51])).
% 3.38/0.81  fof(f51,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(nnf_transformation,[],[f29])).
% 3.38/0.81  fof(f29,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f28])).
% 3.38/0.81  fof(f28,plain,(
% 3.38/0.81    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f4])).
% 3.38/0.81  fof(f4,axiom,(
% 3.38/0.81    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 3.38/0.81  fof(f185,plain,(
% 3.38/0.81    v13_lattices(sK0) | ~spl12_5),
% 3.38/0.81    inference(avatar_component_clause,[],[f184])).
% 3.38/0.81  fof(f507,plain,(
% 3.38/0.81    spl12_32 | spl12_1 | spl12_5 | ~spl12_8 | ~spl12_10),
% 3.38/0.81    inference(avatar_split_clause,[],[f498,f259,f203,f184,f157,f505])).
% 3.38/0.81  fof(f203,plain,(
% 3.38/0.81    spl12_8 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 3.38/0.81  fof(f498,plain,(
% 3.38/0.81    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl12_1 | spl12_5 | ~spl12_8 | ~spl12_10)),
% 3.38/0.81    inference(subsumption_resolution,[],[f222,f260])).
% 3.38/0.81  fof(f222,plain,(
% 3.38/0.81    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0)) ) | (spl12_1 | spl12_5 | ~spl12_8)),
% 3.38/0.81    inference(subsumption_resolution,[],[f221,f159])).
% 3.38/0.81  fof(f221,plain,(
% 3.38/0.81    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl12_5 | ~spl12_8)),
% 3.38/0.81    inference(subsumption_resolution,[],[f212,f186])).
% 3.38/0.81  fof(f212,plain,(
% 3.38/0.81    ( ! [X1] : (sK2(sK0,X1) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,X1))) | v13_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_8),
% 3.38/0.81    inference(resolution,[],[f204,f111])).
% 3.38/0.81  fof(f111,plain,(
% 3.38/0.81    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f59])).
% 3.38/0.81  fof(f204,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0) ) | ~spl12_8),
% 3.38/0.81    inference(avatar_component_clause,[],[f203])).
% 3.38/0.81  fof(f469,plain,(
% 3.38/0.81    spl12_1 | ~spl12_4 | spl12_29),
% 3.38/0.81    inference(avatar_contradiction_clause,[],[f468])).
% 3.38/0.81  fof(f468,plain,(
% 3.38/0.81    $false | (spl12_1 | ~spl12_4 | spl12_29)),
% 3.38/0.81    inference(subsumption_resolution,[],[f467,f159])).
% 3.38/0.81  fof(f467,plain,(
% 3.38/0.81    v2_struct_0(sK0) | (~spl12_4 | spl12_29)),
% 3.38/0.81    inference(subsumption_resolution,[],[f465,f174])).
% 3.38/0.81  fof(f465,plain,(
% 3.38/0.81    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl12_29),
% 3.38/0.81    inference(resolution,[],[f456,f136])).
% 3.38/0.81  fof(f456,plain,(
% 3.38/0.81    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl12_29),
% 3.38/0.81    inference(avatar_component_clause,[],[f454])).
% 3.38/0.81  fof(f388,plain,(
% 3.38/0.81    spl12_24 | spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4),
% 3.38/0.81    inference(avatar_split_clause,[],[f351,f172,f167,f162,f157,f386])).
% 3.38/0.81  fof(f167,plain,(
% 3.38/0.81    spl12_3 <=> v4_lattice3(sK0)),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 3.38/0.81  fof(f351,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0)) ) | (spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f350,f159])).
% 3.38/0.81  fof(f350,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) ) | (~spl12_2 | ~spl12_3 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f349,f164])).
% 3.38/0.81  fof(f349,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl12_3 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f348,f174])).
% 3.38/0.81  fof(f348,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~r4_lattice3(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_3),
% 3.38/0.81    inference(resolution,[],[f345,f169])).
% 3.38/0.81  fof(f169,plain,(
% 3.38/0.81    v4_lattice3(sK0) | ~spl12_3),
% 3.38/0.81    inference(avatar_component_clause,[],[f167])).
% 3.38/0.81  fof(f345,plain,(
% 3.38/0.81    ( ! [X4,X0,X1] : (~v4_lattice3(X0) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(subsumption_resolution,[],[f152,f136])).
% 3.38/0.81  fof(f152,plain,(
% 3.38/0.81    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(duplicate_literal_removal,[],[f146])).
% 3.38/0.81  fof(f146,plain,(
% 3.38/0.81    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(equality_resolution,[],[f123])).
% 3.38/0.81  fof(f123,plain,(
% 3.38/0.81    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f71])).
% 3.38/0.81  fof(f71,plain,(
% 3.38/0.81    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK7(X0,X1,X2)) & r4_lattice3(X0,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f69,f70])).
% 3.38/0.81  fof(f70,plain,(
% 3.38/0.81    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK7(X0,X1,X2)) & r4_lattice3(X0,sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f69,plain,(
% 3.38/0.81    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(rectify,[],[f68])).
% 3.38/0.81  fof(f68,plain,(
% 3.38/0.81    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f67])).
% 3.38/0.81  fof(f67,plain,(
% 3.38/0.81    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(nnf_transformation,[],[f39])).
% 3.38/0.81  fof(f39,plain,(
% 3.38/0.81    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f38])).
% 3.38/0.81  fof(f38,plain,(
% 3.38/0.81    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f11])).
% 3.38/0.81  fof(f11,axiom,(
% 3.38/0.81    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 3.38/0.81  fof(f380,plain,(
% 3.38/0.81    spl12_22 | ~spl12_7),
% 3.38/0.81    inference(avatar_split_clause,[],[f373,f195,f378])).
% 3.38/0.81  fof(f195,plain,(
% 3.38/0.81    spl12_7 <=> ! [X1,X0] : (r2_hidden(sK10(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 3.38/0.81  fof(f373,plain,(
% 3.38/0.81    ( ! [X8] : (~m1_subset_1(X8,u1_struct_0(sK0)) | r4_lattice3(sK0,X8,k1_xboole_0)) ) | ~spl12_7),
% 3.38/0.81    inference(resolution,[],[f196,f176])).
% 3.38/0.81  fof(f176,plain,(
% 3.38/0.81    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.38/0.81    inference(superposition,[],[f135,f148])).
% 3.38/0.81  fof(f148,plain,(
% 3.38/0.81    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.38/0.81    inference(equality_resolution,[],[f139])).
% 3.38/0.81  fof(f139,plain,(
% 3.38/0.81    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.38/0.81    inference(cnf_transformation,[],[f82])).
% 3.38/0.81  fof(f82,plain,(
% 3.38/0.81    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.38/0.81    inference(flattening,[],[f81])).
% 3.38/0.81  fof(f81,plain,(
% 3.38/0.81    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.38/0.81    inference(nnf_transformation,[],[f1])).
% 3.38/0.81  fof(f1,axiom,(
% 3.38/0.81    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.38/0.81  fof(f135,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.38/0.81    inference(cnf_transformation,[],[f2])).
% 3.38/0.81  fof(f2,axiom,(
% 3.38/0.81    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 3.38/0.81  fof(f196,plain,(
% 3.38/0.81    ( ! [X0,X1] : (r2_hidden(sK10(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) ) | ~spl12_7),
% 3.38/0.81    inference(avatar_component_clause,[],[f195])).
% 3.38/0.81  fof(f285,plain,(
% 3.38/0.81    spl12_12 | spl12_1 | ~spl12_4 | ~spl12_11),
% 3.38/0.81    inference(avatar_split_clause,[],[f280,f263,f172,f157,f282])).
% 3.38/0.81  fof(f263,plain,(
% 3.38/0.81    spl12_11 <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 3.38/0.81    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 3.38/0.81  fof(f280,plain,(
% 3.38/0.81    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl12_1 | ~spl12_4 | ~spl12_11)),
% 3.38/0.81    inference(subsumption_resolution,[],[f279,f159])).
% 3.38/0.81  fof(f279,plain,(
% 3.38/0.81    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl12_4 | ~spl12_11)),
% 3.38/0.81    inference(subsumption_resolution,[],[f274,f174])).
% 3.38/0.81  fof(f274,plain,(
% 3.38/0.81    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl12_11),
% 3.38/0.81    inference(superposition,[],[f136,f265])).
% 3.38/0.81  fof(f265,plain,(
% 3.38/0.81    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl12_11),
% 3.38/0.81    inference(avatar_component_clause,[],[f263])).
% 3.38/0.81  fof(f271,plain,(
% 3.38/0.81    ~spl12_4 | spl12_10),
% 3.38/0.81    inference(avatar_contradiction_clause,[],[f270])).
% 3.38/0.81  fof(f270,plain,(
% 3.38/0.81    $false | (~spl12_4 | spl12_10)),
% 3.38/0.81    inference(subsumption_resolution,[],[f268,f174])).
% 3.38/0.81  fof(f268,plain,(
% 3.38/0.81    ~l3_lattices(sK0) | spl12_10),
% 3.38/0.81    inference(resolution,[],[f261,f92])).
% 3.38/0.81  fof(f261,plain,(
% 3.38/0.81    ~l1_lattices(sK0) | spl12_10),
% 3.38/0.81    inference(avatar_component_clause,[],[f259])).
% 3.38/0.81  fof(f266,plain,(
% 3.38/0.81    ~spl12_10 | spl12_11 | spl12_1 | ~spl12_8),
% 3.38/0.81    inference(avatar_split_clause,[],[f218,f203,f157,f263,f259])).
% 3.38/0.81  fof(f218,plain,(
% 3.38/0.81    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | (spl12_1 | ~spl12_8)),
% 3.38/0.81    inference(subsumption_resolution,[],[f210,f159])).
% 3.38/0.81  fof(f210,plain,(
% 3.38/0.81    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl12_8),
% 3.38/0.81    inference(resolution,[],[f204,f103])).
% 3.38/0.81  fof(f205,plain,(
% 3.38/0.81    spl12_8 | spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4),
% 3.38/0.81    inference(avatar_split_clause,[],[f201,f172,f167,f162,f157,f203])).
% 3.38/0.81  fof(f201,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0) ) | (spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f200,f159])).
% 3.38/0.81  fof(f200,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | v2_struct_0(sK0)) ) | (~spl12_2 | ~spl12_3 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f199,f164])).
% 3.38/0.81  fof(f199,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl12_3 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f198,f174])).
% 3.38/0.81  fof(f198,plain,(
% 3.38/0.81    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl12_3),
% 3.38/0.81    inference(resolution,[],[f117,f169])).
% 3.38/0.81  fof(f117,plain,(
% 3.38/0.81    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f35])).
% 3.38/0.81  fof(f35,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f34])).
% 3.38/0.81  fof(f34,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f15])).
% 3.38/0.81  fof(f15,axiom,(
% 3.38/0.81    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).
% 3.38/0.81  fof(f197,plain,(
% 3.38/0.81    spl12_7 | spl12_1 | ~spl12_4),
% 3.38/0.81    inference(avatar_split_clause,[],[f193,f172,f157,f195])).
% 3.38/0.81  fof(f193,plain,(
% 3.38/0.81    ( ! [X0,X1] : (r2_hidden(sK10(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1)) ) | (spl12_1 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f192,f159])).
% 3.38/0.81  fof(f192,plain,(
% 3.38/0.81    ( ! [X0,X1] : (r2_hidden(sK10(sK0,X0,X1),X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r4_lattice3(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl12_4),
% 3.38/0.81    inference(resolution,[],[f133,f174])).
% 3.38/0.81  fof(f133,plain,(
% 3.38/0.81    ( ! [X2,X0,X1] : (~l3_lattices(X0) | r2_hidden(sK10(X0,X1,X2),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 3.38/0.81    inference(cnf_transformation,[],[f80])).
% 3.38/0.81  fof(f80,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK10(X0,X1,X2),X1) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f78,f79])).
% 3.38/0.81  fof(f79,plain,(
% 3.38/0.81    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK10(X0,X1,X2),X1) & r2_hidden(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f78,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(rectify,[],[f77])).
% 3.38/0.81  fof(f77,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(nnf_transformation,[],[f43])).
% 3.38/0.81  fof(f43,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f42])).
% 3.38/0.81  fof(f42,plain,(
% 3.38/0.81    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f10])).
% 3.38/0.81  fof(f10,axiom,(
% 3.38/0.81    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 3.38/0.81  fof(f191,plain,(
% 3.38/0.81    ~spl12_5 | ~spl12_6 | spl12_1 | ~spl12_2 | ~spl12_4),
% 3.38/0.81    inference(avatar_split_clause,[],[f182,f172,f162,f157,f188,f184])).
% 3.38/0.81  fof(f182,plain,(
% 3.38/0.81    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | (spl12_1 | ~spl12_2 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f181,f159])).
% 3.38/0.81  fof(f181,plain,(
% 3.38/0.81    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | v2_struct_0(sK0) | (~spl12_2 | ~spl12_4)),
% 3.38/0.81    inference(subsumption_resolution,[],[f180,f164])).
% 3.38/0.81  fof(f180,plain,(
% 3.38/0.81    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl12_4),
% 3.38/0.81    inference(subsumption_resolution,[],[f91,f174])).
% 3.38/0.81  fof(f91,plain,(
% 3.38/0.81    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 3.38/0.81    inference(cnf_transformation,[],[f49])).
% 3.38/0.81  fof(f49,plain,(
% 3.38/0.81    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 3.38/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f48])).
% 3.38/0.81  fof(f48,plain,(
% 3.38/0.81    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 3.38/0.81    introduced(choice_axiom,[])).
% 3.38/0.81  fof(f20,plain,(
% 3.38/0.81    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.38/0.81    inference(flattening,[],[f19])).
% 3.38/0.81  fof(f19,plain,(
% 3.38/0.81    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.38/0.81    inference(ennf_transformation,[],[f18])).
% 3.38/0.81  fof(f18,negated_conjecture,(
% 3.38/0.81    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.38/0.81    inference(negated_conjecture,[],[f17])).
% 3.38/0.81  fof(f17,conjecture,(
% 3.38/0.81    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.38/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 3.38/0.81  fof(f175,plain,(
% 3.38/0.81    spl12_4),
% 3.38/0.81    inference(avatar_split_clause,[],[f90,f172])).
% 3.38/0.81  fof(f90,plain,(
% 3.38/0.81    l3_lattices(sK0)),
% 3.38/0.81    inference(cnf_transformation,[],[f49])).
% 3.38/0.81  fof(f170,plain,(
% 3.38/0.81    spl12_3),
% 3.38/0.81    inference(avatar_split_clause,[],[f89,f167])).
% 3.38/0.81  fof(f89,plain,(
% 3.38/0.81    v4_lattice3(sK0)),
% 3.38/0.81    inference(cnf_transformation,[],[f49])).
% 3.38/0.81  fof(f165,plain,(
% 3.38/0.81    spl12_2),
% 3.38/0.81    inference(avatar_split_clause,[],[f88,f162])).
% 3.38/0.81  fof(f88,plain,(
% 3.38/0.81    v10_lattices(sK0)),
% 3.38/0.81    inference(cnf_transformation,[],[f49])).
% 3.38/0.81  fof(f160,plain,(
% 3.38/0.81    ~spl12_1),
% 3.38/0.81    inference(avatar_split_clause,[],[f87,f157])).
% 3.38/0.81  fof(f87,plain,(
% 3.38/0.81    ~v2_struct_0(sK0)),
% 3.38/0.81    inference(cnf_transformation,[],[f49])).
% 3.38/0.81  % SZS output end Proof for theBenchmark
% 3.38/0.81  % (13324)------------------------------
% 3.38/0.81  % (13324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.38/0.81  % (13324)Termination reason: Refutation
% 3.38/0.81  
% 3.38/0.81  % (13324)Memory used [KB]: 9594
% 3.38/0.81  % (13324)Time elapsed: 0.388 s
% 3.38/0.81  % (13324)------------------------------
% 3.38/0.81  % (13324)------------------------------
% 3.38/0.81  % (13321)Success in time 0.448 s
%------------------------------------------------------------------------------
