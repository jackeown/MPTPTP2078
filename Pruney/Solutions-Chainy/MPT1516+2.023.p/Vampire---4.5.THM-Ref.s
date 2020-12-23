%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 375 expanded)
%              Number of leaves         :   32 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          : 1004 (1648 expanded)
%              Number of equality atoms :   89 ( 143 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f136,f152,f167,f172,f175,f188,f193,f222,f244,f256,f301,f307,f363,f407])).

fof(f407,plain,
    ( spl9_1
    | spl9_5
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl9_1
    | spl9_5
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f405,f242])).

fof(f242,plain,
    ( m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl9_17
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f405,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | spl9_5
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f404,f357])).

fof(f357,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl9_23
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f404,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | spl9_5
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f392,f131])).

fof(f131,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl9_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f392,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_23 ),
    inference(superposition,[],[f272,f385])).

fof(f385,plain,
    ( ! [X4] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_6
    | ~ spl9_11
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f322,f357])).

fof(f322,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f321,f92])).

fof(f92,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f321,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f312,f165])).

fof(f165,plain,
    ( l1_lattices(sK0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl9_11
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f312,plain,
    ( ! [X4] :
        ( ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) )
    | ~ spl9_6 ),
    inference(resolution,[],[f134,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X2,X1) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f134,plain,
    ( v13_lattices(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl9_6
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f272,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f271,f242])).

fof(f271,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_13
    | ~ spl9_16 ),
    inference(superposition,[],[f187,f239])).

fof(f239,plain,
    ( ! [X1] :
        ( k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl9_16
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f187,plain,
    ( ! [X8,X7] :
        ( k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl9_13
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f363,plain,
    ( spl9_1
    | ~ spl9_11
    | spl9_23 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl9_1
    | ~ spl9_11
    | spl9_23 ),
    inference(subsumption_resolution,[],[f361,f92])).

fof(f361,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_11
    | spl9_23 ),
    inference(subsumption_resolution,[],[f360,f165])).

fof(f360,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_23 ),
    inference(resolution,[],[f358,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f358,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f356])).

fof(f307,plain,
    ( spl9_1
    | spl9_6
    | ~ spl9_11
    | ~ spl9_17
    | spl9_19 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl9_1
    | spl9_6
    | ~ spl9_11
    | ~ spl9_17
    | spl9_19 ),
    inference(subsumption_resolution,[],[f305,f135])).

fof(f135,plain,
    ( ~ v13_lattices(sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f305,plain,
    ( v13_lattices(sK0)
    | spl9_1
    | ~ spl9_11
    | ~ spl9_17
    | spl9_19 ),
    inference(subsumption_resolution,[],[f304,f92])).

fof(f304,plain,
    ( v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_11
    | ~ spl9_17
    | spl9_19 ),
    inference(subsumption_resolution,[],[f303,f242])).

fof(f303,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_11
    | spl9_19 ),
    inference(subsumption_resolution,[],[f302,f165])).

fof(f302,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | spl9_19 ),
    inference(resolution,[],[f300,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f300,plain,
    ( ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl9_19
  <=> m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f301,plain,
    ( ~ spl9_19
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f296,f241,f238,f186,f164,f161,f133,f90,f298])).

fof(f161,plain,
    ( spl9_10
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f296,plain,
    ( ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f287,f242])).

fof(f287,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(trivial_inequality_removal,[],[f286])).

fof(f286,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(superposition,[],[f206,f272])).

fof(f206,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK4(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f205,f135])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0
        | v13_lattices(sK0) )
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f204,f92])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f203,f165])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(resolution,[],[f200,f72])).

fof(f200,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,sK4(sK0,X1)) != X1 )
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ! [X1] :
        ( k2_lattices(sK0,X1,sK4(sK0,X1)) != X1
        | k2_lattices(sK0,X1,sK4(sK0,X1)) != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl9_1
    | spl9_6
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(superposition,[],[f197,f162])).

fof(f162,plain,
    ( ! [X6,X5] :
        ( k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f161])).

fof(f197,plain,
    ( ! [X4] :
        ( k2_lattices(sK0,sK4(sK0,X4),X4) != X4
        | k2_lattices(sK0,X4,sK4(sK0,X4)) != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl9_1
    | spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f196,f135])).

fof(f196,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,sK4(sK0,X4)) != X4
        | k2_lattices(sK0,sK4(sK0,X4),X4) != X4
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f111,f165])).

fof(f111,plain,
    ( ! [X4] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_lattices(sK0,X4,sK4(sK0,X4)) != X4
        | k2_lattices(sK0,sK4(sK0,X4),X4) != X4
        | v13_lattices(sK0) )
    | spl9_1 ),
    inference(resolution,[],[f92,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK4(X0,X1)) != X1
      | k2_lattices(X0,sK4(X0,X1),X1) != X1
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f256,plain,
    ( spl9_1
    | ~ spl9_4
    | spl9_17 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | spl9_17 ),
    inference(subsumption_resolution,[],[f254,f92])).

fof(f254,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_4
    | spl9_17 ),
    inference(subsumption_resolution,[],[f253,f107])).

fof(f107,plain,
    ( l3_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f253,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_17 ),
    inference(resolution,[],[f243,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f243,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f241])).

fof(f244,plain,
    ( spl9_16
    | ~ spl9_17
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f234,f214,f182,f157,f146,f105,f100,f95,f90,f241,f238])).

fof(f95,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f100,plain,
    ( spl9_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f146,plain,
    ( spl9_8
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f157,plain,
    ( spl9_9
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f182,plain,
    ( spl9_12
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f214,plain,
    ( spl9_15
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f234,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1 )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(resolution,[],[f228,f155])).

fof(f155,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f153,f137])).

fof(f137,plain,
    ( ! [X5] :
        ( k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f125,f107])).

fof(f125,plain,
    ( ! [X5] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5 )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f124,f92])).

fof(f124,plain,
    ( ! [X5] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5 )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f118,f97])).

fof(f97,plain,
    ( v10_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f118,plain,
    ( ! [X5] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5 )
    | ~ spl9_3 ),
    inference(resolution,[],[f102,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

fof(f102,plain,
    ( v4_lattice3(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f153,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f141,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1(sK0,X0,X1))
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f140,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f140,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK1(sK0,X3,X4),X3)
        | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f123,f107])).

fof(f123,plain,
    ( ! [X4,X3] :
        ( ~ l3_lattices(sK0)
        | r2_hidden(sK1(sK0,X3,X4),X3)
        | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f122,f92])).

fof(f122,plain,
    ( ! [X4,X3] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | r2_hidden(sK1(sK0,X3,X4),X3)
        | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4)) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f117,f97])).

fof(f117,plain,
    ( ! [X4,X3] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | r2_hidden(sK1(sK0,X3,X4),X3)
        | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f102,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,X1,X0) = X0 )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,X1,X0) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(resolution,[],[f226,f154])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,X3) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f110,f147])).

fof(f147,plain,
    ( l2_lattices(sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f110,plain,
    ( ! [X2,X3] :
        ( ~ l2_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k1_lattices(sK0,X2,X3) = X3
        | ~ r1_lattices(sK0,X2,X3) )
    | spl9_1 ),
    inference(resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f226,plain,
    ( ! [X12,X11] :
        ( r1_lattices(sK0,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X11,X12) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f225,f107])).

fof(f225,plain,
    ( ! [X12,X11] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattices(sK0,X11,X12)
        | ~ r3_lattices(sK0,X11,X12) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f224,f183])).

fof(f183,plain,
    ( v9_lattices(sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f224,plain,
    ( ! [X12,X11] :
        ( ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattices(sK0,X11,X12)
        | ~ r3_lattices(sK0,X11,X12) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f223,f215])).

fof(f215,plain,
    ( v8_lattices(sK0)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f214])).

fof(f223,plain,
    ( ! [X12,X11] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattices(sK0,X11,X12)
        | ~ r3_lattices(sK0,X11,X12) )
    | spl9_1
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f115,f158])).

fof(f158,plain,
    ( v6_lattices(sK0)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f115,plain,
    ( ! [X12,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattices(sK0,X11,X12)
        | ~ r3_lattices(sK0,X11,X12) )
    | spl9_1 ),
    inference(resolution,[],[f92,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

% (15029)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f41,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f222,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_15 ),
    inference(subsumption_resolution,[],[f220,f107])).

fof(f220,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_15 ),
    inference(subsumption_resolution,[],[f219,f97])).

fof(f219,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_15 ),
    inference(subsumption_resolution,[],[f218,f92])).

fof(f218,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_15 ),
    inference(resolution,[],[f216,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f216,plain,
    ( ~ v8_lattices(sK0)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f214])).

fof(f193,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_12 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_12 ),
    inference(subsumption_resolution,[],[f191,f107])).

fof(f191,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_12 ),
    inference(subsumption_resolution,[],[f190,f97])).

fof(f190,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_12 ),
    inference(subsumption_resolution,[],[f189,f92])).

fof(f189,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_12 ),
    inference(resolution,[],[f184,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f184,plain,
    ( ~ v9_lattices(sK0)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f188,plain,
    ( ~ spl9_12
    | spl9_13
    | spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f180,f105,f90,f186,f182])).

fof(f180,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7
        | ~ v9_lattices(sK0) )
    | spl9_1
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f113,f107])).

fof(f113,plain,
    ( ! [X8,X7] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7
        | ~ v9_lattices(sK0) )
    | spl9_1 ),
    inference(resolution,[],[f92,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | ~ v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f175,plain,
    ( ~ spl9_4
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl9_4
    | spl9_11 ),
    inference(subsumption_resolution,[],[f173,f107])).

fof(f173,plain,
    ( ~ l3_lattices(sK0)
    | spl9_11 ),
    inference(resolution,[],[f166,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f166,plain,
    ( ~ l1_lattices(sK0)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f164])).

fof(f172,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_9 ),
    inference(subsumption_resolution,[],[f170,f107])).

fof(f170,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_9 ),
    inference(subsumption_resolution,[],[f169,f97])).

fof(f169,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_9 ),
    inference(subsumption_resolution,[],[f168,f92])).

fof(f168,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_9 ),
    inference(resolution,[],[f159,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f159,plain,
    ( ~ v6_lattices(sK0)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f167,plain,
    ( ~ spl9_9
    | spl9_10
    | ~ spl9_11
    | spl9_1 ),
    inference(avatar_split_clause,[],[f112,f90,f164,f161,f157])).

fof(f112,plain,
    ( ! [X6,X5] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5)
        | ~ v6_lattices(sK0) )
    | spl9_1 ),
    inference(resolution,[],[f92,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f152,plain,
    ( ~ spl9_4
    | spl9_8 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl9_4
    | spl9_8 ),
    inference(subsumption_resolution,[],[f150,f107])).

fof(f150,plain,
    ( ~ l3_lattices(sK0)
    | spl9_8 ),
    inference(resolution,[],[f148,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f148,plain,
    ( ~ l2_lattices(sK0)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f136,plain,
    ( ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f88,f133,f129])).

fof(f88,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(global_subsumption,[],[f47,f45,f44,f43])).

fof(f43,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f47,f105])).

fof(f103,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f46,f100])).

fof(f46,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f45,f95])).

fof(f93,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f44,f90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:27:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (15025)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (15021)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (15013)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (15021)Refutation not found, incomplete strategy% (15021)------------------------------
% 0.22/0.49  % (15021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15021)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15021)Memory used [KB]: 6268
% 0.22/0.49  % (15021)Time elapsed: 0.062 s
% 0.22/0.49  % (15021)------------------------------
% 0.22/0.49  % (15021)------------------------------
% 0.22/0.49  % (15017)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (15024)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (15030)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (15011)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (15031)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (15014)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (15031)Refutation not found, incomplete strategy% (15031)------------------------------
% 0.22/0.50  % (15031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15031)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15031)Memory used [KB]: 10618
% 0.22/0.50  % (15031)Time elapsed: 0.081 s
% 0.22/0.50  % (15031)------------------------------
% 0.22/0.50  % (15031)------------------------------
% 0.22/0.50  % (15026)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (15016)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (15014)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (15018)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f410,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f136,f152,f167,f172,f175,f188,f193,f222,f244,f256,f301,f307,f363,f407])).
% 0.22/0.50  fof(f407,plain,(
% 0.22/0.50    spl9_1 | spl9_5 | ~spl9_6 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_23),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f406])).
% 0.22/0.50  fof(f406,plain,(
% 0.22/0.50    $false | (spl9_1 | spl9_5 | ~spl9_6 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f405,f242])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~spl9_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f241])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    spl9_17 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.22/0.50  fof(f405,plain,(
% 0.22/0.50    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | spl9_5 | ~spl9_6 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f404,f357])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl9_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f356])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    spl9_23 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.22/0.50  fof(f404,plain,(
% 0.22/0.50    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | spl9_5 | ~spl9_6 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f392,f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl9_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl9_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.50  fof(f392,plain,(
% 0.22/0.50    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_6 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17 | ~spl9_23)),
% 0.22/0.50    inference(superposition,[],[f272,f385])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    ( ! [X4] : (k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_6 | ~spl9_11 | ~spl9_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f322,f357])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    ( ! [X4] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | (spl9_1 | ~spl9_6 | ~spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f321,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ~v2_struct_0(sK0) | spl9_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl9_1 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    ( ! [X4] : (v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | (~spl9_6 | ~spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f312,f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    l1_lattices(sK0) | ~spl9_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f164])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    spl9_11 <=> l1_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    ( ! [X4] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X4,k5_lattices(sK0))) ) | ~spl9_6),
% 0.22/0.50    inference(resolution,[],[f134,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X2,X0] : (~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X2,X1) = X1 | k5_lattices(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    v13_lattices(sK0) | ~spl9_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl9_6 <=> v13_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_13 | ~spl9_16 | ~spl9_17)),
% 0.22/0.50    inference(subsumption_resolution,[],[f271,f242])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_13 | ~spl9_16)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f267])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl9_13 | ~spl9_16)),
% 0.22/0.50    inference(superposition,[],[f187,f239])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ( ! [X1] : (k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl9_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f238])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl9_16 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ( ! [X8,X7] : (k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7 | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | ~spl9_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f186])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    spl9_13 <=> ! [X7,X8] : (~m1_subset_1(X7,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7 | ~m1_subset_1(X8,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.50  fof(f363,plain,(
% 0.22/0.50    spl9_1 | ~spl9_11 | spl9_23),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f362])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    $false | (spl9_1 | ~spl9_11 | spl9_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f361,f92])).
% 0.22/0.50  fof(f361,plain,(
% 0.22/0.50    v2_struct_0(sK0) | (~spl9_11 | spl9_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f360,f165])).
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl9_23),
% 0.22/0.50    inference(resolution,[],[f358,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl9_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f356])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    spl9_1 | spl9_6 | ~spl9_11 | ~spl9_17 | spl9_19),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f306])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    $false | (spl9_1 | spl9_6 | ~spl9_11 | ~spl9_17 | spl9_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f305,f135])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ~v13_lattices(sK0) | spl9_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    v13_lattices(sK0) | (spl9_1 | ~spl9_11 | ~spl9_17 | spl9_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f304,f92])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v13_lattices(sK0) | (~spl9_11 | ~spl9_17 | spl9_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f303,f242])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | (~spl9_11 | spl9_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f302,f165])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | spl9_19),
% 0.22/0.50    inference(resolution,[],[f300,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | spl9_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f298])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    spl9_19 <=> m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    ~spl9_19 | spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f296,f241,f238,f186,f164,f161,f133,f90,f298])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl9_10 <=> ! [X5,X6] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5) | ~m1_subset_1(X6,u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    ~m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17)),
% 0.22/0.50    inference(subsumption_resolution,[],[f287,f242])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f286])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11 | ~spl9_13 | ~spl9_16 | ~spl9_17)),
% 0.22/0.50    inference(superposition,[],[f206,f272])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ( ! [X0] : (k2_lattices(sK0,X0,sK4(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f205,f135])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0 | v13_lattices(sK0)) ) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f204,f92])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0 | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f203,f165])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0 | ~l1_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f202])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK4(sK0,X0)) != X0 | ~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11)),
% 0.22/0.50    inference(resolution,[],[f200,f72])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(sK4(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,sK4(sK0,X1)) != X1) ) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f199])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ( ! [X1] : (k2_lattices(sK0,X1,sK4(sK0,X1)) != X1 | k2_lattices(sK0,X1,sK4(sK0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl9_1 | spl9_6 | ~spl9_10 | ~spl9_11)),
% 0.22/0.50    inference(superposition,[],[f197,f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X6,X5] : (k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | ~spl9_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X4] : (k2_lattices(sK0,sK4(sK0,X4),X4) != X4 | k2_lattices(sK0,X4,sK4(sK0,X4)) != X4 | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl9_1 | spl9_6 | ~spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f196,f135])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,sK4(sK0,X4)) != X4 | k2_lattices(sK0,sK4(sK0,X4),X4) != X4 | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f111,f165])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ( ! [X4] : (~l1_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_lattices(sK0,X4,sK4(sK0,X4)) != X4 | k2_lattices(sK0,sK4(sK0,X4),X4) != X4 | v13_lattices(sK0)) ) | spl9_1),
% 0.22/0.50    inference(resolution,[],[f92,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK4(X0,X1)) != X1 | k2_lattices(X0,sK4(X0,X1),X1) != X1 | v13_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    spl9_1 | ~spl9_4 | spl9_17),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f255])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    $false | (spl9_1 | ~spl9_4 | spl9_17)),
% 0.22/0.50    inference(subsumption_resolution,[],[f254,f92])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    v2_struct_0(sK0) | (~spl9_4 | spl9_17)),
% 0.22/0.50    inference(subsumption_resolution,[],[f253,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    l3_lattices(sK0) | ~spl9_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl9_4 <=> l3_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl9_17),
% 0.22/0.50    inference(resolution,[],[f243,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl9_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f241])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    spl9_16 | ~spl9_17 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f234,f214,f182,f157,f146,f105,f100,f95,f90,f241,f238])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl9_2 <=> v10_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl9_3 <=> v4_lattice3(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl9_8 <=> l2_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl9_9 <=> v6_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    spl9_12 <=> v9_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    spl9_15 <=> v8_lattices(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_15)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f231])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_15)),
% 0.22/0.50    inference(resolution,[],[f228,f155])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 0.22/0.50    inference(superposition,[],[f153,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X5] : (k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5 | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f125,f107])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X5] : (~l3_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5) ) | (spl9_1 | ~spl9_2 | ~spl9_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f124,f92])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ( ! [X5] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5) ) | (~spl9_2 | ~spl9_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    v10_lattices(sK0) | ~spl9_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X5] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X5)) = X5) ) | ~spl9_3),
% 0.22/0.50    inference(resolution,[],[f102,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    v4_lattice3(sK0) | ~spl9_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f100])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 0.22/0.50    inference(resolution,[],[f141,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,sK1(sK0,X0,X1)) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 0.22/0.50    inference(resolution,[],[f140,f83])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ( ! [X4,X3] : (r2_hidden(sK1(sK0,X3,X4),X3) | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f107])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X4,X3] : (~l3_lattices(sK0) | r2_hidden(sK1(sK0,X3,X4),X3) | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4))) ) | (spl9_1 | ~spl9_2 | ~spl9_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f122,f92])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X4,X3] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | r2_hidden(sK1(sK0,X3,X4),X3) | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4))) ) | (~spl9_2 | ~spl9_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f97])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X4,X3] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | r2_hidden(sK1(sK0,X3,X4),X3) | r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4))) ) | ~spl9_3),
% 0.22/0.50    inference(resolution,[],[f102,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | r2_hidden(sK1(X0,X1,X2),X1) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X1,X0) = X0) ) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_15)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f227])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X1,X0) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_12 | ~spl9_15)),
% 0.22/0.50    inference(resolution,[],[f226,f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~r1_lattices(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X2,X3) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f147])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    l2_lattices(sK0) | ~spl9_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f146])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~l2_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k1_lattices(sK0,X2,X3) = X3 | ~r1_lattices(sK0,X2,X3)) ) | spl9_1),
% 0.22/0.50    inference(resolution,[],[f92,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ( ! [X12,X11] : (r1_lattices(sK0,X11,X12) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r3_lattices(sK0,X11,X12)) ) | (spl9_1 | ~spl9_4 | ~spl9_9 | ~spl9_12 | ~spl9_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f225,f107])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ( ! [X12,X11] : (~l3_lattices(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | r1_lattices(sK0,X11,X12) | ~r3_lattices(sK0,X11,X12)) ) | (spl9_1 | ~spl9_9 | ~spl9_12 | ~spl9_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f224,f183])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    v9_lattices(sK0) | ~spl9_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f182])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ( ! [X12,X11] : (~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | r1_lattices(sK0,X11,X12) | ~r3_lattices(sK0,X11,X12)) ) | (spl9_1 | ~spl9_9 | ~spl9_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f223,f215])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    v8_lattices(sK0) | ~spl9_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f214])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ( ! [X12,X11] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | r1_lattices(sK0,X11,X12) | ~r3_lattices(sK0,X11,X12)) ) | (spl9_1 | ~spl9_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f115,f158])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    v6_lattices(sK0) | ~spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f157])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ( ! [X12,X11] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | r1_lattices(sK0,X11,X12) | ~r3_lattices(sK0,X11,X12)) ) | spl9_1),
% 0.22/0.50    inference(resolution,[],[f92,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f41])).
% 0.22/0.50  % (15029)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_15),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f221])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f220,f107])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f219,f97])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f218,f92])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_15),
% 0.22/0.50    inference(resolution,[],[f216,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    ~v8_lattices(sK0) | spl9_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f214])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_12),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f191,f107])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f190,f97])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_12)),
% 0.22/0.50    inference(subsumption_resolution,[],[f189,f92])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_12),
% 0.22/0.50    inference(resolution,[],[f184,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ~v9_lattices(sK0) | spl9_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f182])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ~spl9_12 | spl9_13 | spl9_1 | ~spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f180,f105,f90,f186,f182])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X8,X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7 | ~v9_lattices(sK0)) ) | (spl9_1 | ~spl9_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f113,f107])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X8,X7] : (~l3_lattices(sK0) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | k2_lattices(sK0,X7,k1_lattices(sK0,X7,X8)) = X7 | ~v9_lattices(sK0)) ) | spl9_1),
% 0.22/0.50    inference(resolution,[],[f92,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~v9_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ~spl9_4 | spl9_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    $false | (~spl9_4 | spl9_11)),
% 0.22/0.50    inference(subsumption_resolution,[],[f173,f107])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ~l3_lattices(sK0) | spl9_11),
% 0.22/0.50    inference(resolution,[],[f166,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ~l1_lattices(sK0) | spl9_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f164])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f170,f107])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f169,f97])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f168,f92])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_9),
% 0.22/0.50    inference(resolution,[],[f159,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ~v6_lattices(sK0) | spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f157])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ~spl9_9 | spl9_10 | ~spl9_11 | spl9_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f112,f90,f164,f161,f157])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X6,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_lattices(sK0,X5,X6) = k2_lattices(sK0,X6,X5) | ~v6_lattices(sK0)) ) | spl9_1),
% 0.22/0.50    inference(resolution,[],[f92,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~v6_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    ~spl9_4 | spl9_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f151])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    $false | (~spl9_4 | spl9_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f150,f107])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    ~l3_lattices(sK0) | spl9_8),
% 0.22/0.50    inference(resolution,[],[f148,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    ~l2_lattices(sK0) | spl9_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f146])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ~spl9_5 | ~spl9_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f88,f133,f129])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 0.22/0.50    inference(global_subsumption,[],[f47,f45,f44,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f15])).
% 0.22/0.50  fof(f15,conjecture,(
% 0.22/0.50    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    v10_lattices(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    l3_lattices(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f47,f105])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl9_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f100])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    v4_lattice3(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f95])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~spl9_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f90])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15014)------------------------------
% 0.22/0.50  % (15014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15014)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15014)Memory used [KB]: 10746
% 0.22/0.50  % (15014)Time elapsed: 0.088 s
% 0.22/0.50  % (15014)------------------------------
% 0.22/0.50  % (15014)------------------------------
% 0.22/0.50  % (15028)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (15012)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (15027)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (15015)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (15012)Refutation not found, incomplete strategy% (15012)------------------------------
% 0.22/0.51  % (15012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15012)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15012)Memory used [KB]: 10618
% 0.22/0.51  % (15012)Time elapsed: 0.092 s
% 0.22/0.51  % (15012)------------------------------
% 0.22/0.51  % (15012)------------------------------
% 0.22/0.51  % (15011)Refutation not found, incomplete strategy% (15011)------------------------------
% 0.22/0.51  % (15011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15011)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15011)Memory used [KB]: 6140
% 0.22/0.51  % (15011)Time elapsed: 0.092 s
% 0.22/0.51  % (15011)------------------------------
% 0.22/0.51  % (15011)------------------------------
% 0.22/0.51  % (15020)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (15010)Success in time 0.151 s
%------------------------------------------------------------------------------
