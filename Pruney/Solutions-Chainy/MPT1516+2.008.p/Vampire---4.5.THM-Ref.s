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
% DateTime   : Thu Dec  3 13:15:48 EST 2020

% Result     : Theorem 10.59s
% Output     : Refutation 10.59s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 877 expanded)
%              Number of leaves         :   50 ( 319 expanded)
%              Depth                    :   21
%              Number of atoms          : 1692 (4088 expanded)
%              Number of equality atoms :  197 ( 400 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f244,f245,f250,f251,f252,f410,f415,f420,f425,f497,f720,f1063,f5267,f5534,f5698,f10819,f21221])).

fof(f21221,plain,
    ( spl17_1
    | ~ spl17_2
    | spl17_3
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10 ),
    inference(avatar_contradiction_clause,[],[f21220])).

fof(f21220,plain,
    ( $false
    | spl17_1
    | ~ spl17_2
    | spl17_3
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f21189,f567])).

fof(f567,plain,
    ( ! [X0] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
    | spl17_1
    | spl17_3
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(unit_resulting_resolution,[],[f226,f424,f235,f358,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f84,f86,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
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

fof(f84,plain,(
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
    inference(rectify,[],[f83])).

fof(f83,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f358,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl17_1
    | ~ spl17_4 ),
    inference(unit_resulting_resolution,[],[f226,f238,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f238,plain,
    ( l3_lattices(sK0)
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl17_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f235,plain,
    ( ~ v13_lattices(sK0)
    | spl17_3 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl17_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f424,plain,
    ( l1_lattices(sK0)
    | ~ spl17_10 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl17_10
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f226,plain,
    ( ~ v2_struct_0(sK0)
    | spl17_1 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl17_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f21189,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl17_1
    | ~ spl17_2
    | spl17_3
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_10 ),
    inference(unit_resulting_resolution,[],[f226,f414,f409,f238,f358,f11271,f11815,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f11815,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl17_1
    | spl17_3
    | ~ spl17_4
    | ~ spl17_9
    | ~ spl17_10 ),
    inference(duplicate_literal_removal,[],[f11811])).

fof(f11811,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) )
    | spl17_1
    | spl17_3
    | ~ spl17_4
    | ~ spl17_9
    | ~ spl17_10 ),
    inference(superposition,[],[f619,f1391])).

fof(f1391,plain,
    ( ! [X0,X1] : k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))
    | spl17_1
    | spl17_3
    | ~ spl17_4
    | ~ spl17_9
    | ~ spl17_10 ),
    inference(unit_resulting_resolution,[],[f226,f424,f419,f358,f567,f155])).

fof(f155,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f89,f91,f90])).

fof(f90,plain,(
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

fof(f91,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
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
    inference(rectify,[],[f88])).

fof(f88,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f419,plain,
    ( v6_lattices(sK0)
    | ~ spl17_9 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl17_9
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_9])])).

fof(f619,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) )
    | spl17_1
    | spl17_3
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f618,f226])).

fof(f618,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | v2_struct_0(sK0) )
    | spl17_1
    | spl17_3
    | ~ spl17_4
    | ~ spl17_10 ),
    inference(subsumption_resolution,[],[f617,f424])).

fof(f617,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | spl17_3
    | ~ spl17_4 ),
    inference(subsumption_resolution,[],[f585,f235])).

fof(f585,plain,
    ( ! [X16] :
        ( v13_lattices(sK0)
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_4 ),
    inference(resolution,[],[f358,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f11271,plain,
    ( ! [X4] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X4)))
    | spl17_1
    | ~ spl17_2
    | spl17_3
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(superposition,[],[f8412,f1402])).

fof(f1402,plain,
    ( ! [X0] : sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,k15_lattice3(sK0,X0))))
    | spl17_1
    | ~ spl17_2
    | spl17_3
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_10 ),
    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f567,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f249,plain,
    ( v4_lattice3(sK0)
    | ~ spl17_6 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl17_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f230,plain,
    ( v10_lattices(sK0)
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl17_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f8412,plain,
    ( ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f238,f358,f358,f1503,f5229,f178])).

% (9204)Time limit reached!
% (9204)------------------------------
% (9204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9204)Termination reason: Time limit

fof(f178,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

% (9204)Memory used [KB]: 20596
% (9204)Time elapsed: 1.324 s
% (9204)------------------------------
% (9204)------------------------------
fof(f108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK9(X0,X1,X2))
                  & r2_hidden(sK9(X0,X1,X2),X2)
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f106,f107])).

fof(f107,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f5229,plain,
    ( ! [X0] : r2_hidden(k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f860,f358,f358,f5120,f217])).

fof(f217,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_6_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f201])).

fof(f201,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r3_lattices(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK14(X0,X1,X2),X2)
            & r3_lattices(X1,sK14(X0,X1,X2),sK13(X0,X1,X2))
            & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))
            & sK13(X0,X1,X2) = X0
            & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f122,f124,f123])).

fof(f123,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r3_lattices(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r3_lattices(X1,X6,sK13(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK13(X0,X1,X2) = X0
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f124,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,X6,sK13(X0,X1,X2))
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK14(X0,X1,X2),X2)
        & r3_lattices(X1,sK14(X0,X1,X2),sK13(X0,X1,X2))
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r3_lattices(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f121])).

fof(f121,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).

fof(f5120,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f136,f1808])).

fof(f1808,plain,
    ( ! [X14,X15] :
        ( ~ r1_tarski(X14,sK7(sK0,X14,a_2_5_lattice3(sK0,X15)))
        | r3_lattices(sK0,k15_lattice3(sK0,X14),k15_lattice3(sK0,X15)) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(resolution,[],[f806,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f806,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f805,f226])).

fof(f805,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f804,f230])).

fof(f804,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f803,f249])).

fof(f803,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f780,f238])).

fof(f780,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(superposition,[],[f171,f427])).

fof(f427,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f230,f238,f249,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK7(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK7(X0,X1,X2),X1)
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f59,f98])).

fof(f98,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X2)
            | ~ r3_lattices(X0,sK7(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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

fof(f136,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f860,plain,
    ( ! [X0] : r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f358,f566,f216])).

fof(f216,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f195])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK12(X0,X1,X2),X2)
            & sK12(X0,X1,X2) = X0
            & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f118,f119])).

fof(f119,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK12(X0,X1,X2),X2)
        & sK12(X0,X1,X2) = X0
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X4] :
              ( r4_lattice3(X1,X4,X2)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( r4_lattice3(X1,X3,X2)
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f566,plain,
    ( ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f358,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK8(X0,X1,X2))
                & r4_lattice3(X0,sK8(X0,X1,X2),X1)
                & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f102,f103])).

fof(f103,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK8(X0,X1,X2))
        & r4_lattice3(X0,sK8(X0,X1,X2),X1)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
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
    inference(rectify,[],[f101])).

fof(f101,plain,(
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
    inference(flattening,[],[f100])).

fof(f100,plain,(
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
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f1503,plain,
    ( ! [X0] : r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0)))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(superposition,[],[f859,f426])).

fof(f426,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f230,f238,f249,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f859,plain,
    ( ! [X17] : r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f858,f226])).

fof(f858,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f857,f230])).

fof(f857,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f856,f249])).

fof(f856,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f855,f238])).

fof(f855,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f844,f357])).

fof(f357,plain,
    ( ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl17_1
    | ~ spl17_4 ),
    inference(unit_resulting_resolution,[],[f226,f238,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f844,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ m1_subset_1(k16_lattice3(sK0,X17),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(superposition,[],[f211,f428])).

fof(f428,plain,
    ( ! [X0] : k16_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f230,f238,f249,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f211,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
                  & r3_lattice3(X0,sK6(X0,X1,X2),X2)
                  & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f95,f96])).

fof(f96,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
        & r3_lattice3(X0,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X4] :
                      ( r3_lattices(X0,X4,X1)
                      | ~ r3_lattice3(X0,X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k16_lattice3(X0,X2) = X1
                | ? [X3] :
                    ( ~ r3_lattices(X0,X3,X1)
                    & r3_lattice3(X0,X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) )
              & ( ( ! [X3] :
                      ( r3_lattices(X0,X3,X1)
                      | ~ r3_lattice3(X0,X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f409,plain,
    ( v9_lattices(sK0)
    | ~ spl17_7 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl17_7
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).

fof(f414,plain,
    ( v8_lattices(sK0)
    | ~ spl17_8 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl17_8
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f10819,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_11
    | ~ spl17_35
    | ~ spl17_170 ),
    inference(avatar_contradiction_clause,[],[f10818])).

fof(f10818,plain,
    ( $false
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_11
    | ~ spl17_35
    | ~ spl17_170 ),
    inference(subsumption_resolution,[],[f10817,f243])).

fof(f243,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl17_5 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl17_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).

fof(f10817,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_11
    | ~ spl17_35
    | ~ spl17_170 ),
    inference(forward_demodulation,[],[f10816,f3079])).

fof(f3079,plain,
    ( ! [X0] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_35 ),
    inference(superposition,[],[f1062,f426])).

fof(f1062,plain,
    ( ! [X44] : k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
    | ~ spl17_35 ),
    inference(avatar_component_clause,[],[f1061])).

fof(f1061,plain,
    ( spl17_35
  <=> ! [X44] : k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_35])])).

fof(f10816,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl17_1
    | ~ spl17_4
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_11
    | ~ spl17_170 ),
    inference(subsumption_resolution,[],[f10815,f226])).

fof(f10815,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | spl17_1
    | ~ spl17_4
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_11
    | ~ spl17_170 ),
    inference(subsumption_resolution,[],[f10814,f414])).

fof(f10814,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl17_1
    | ~ spl17_4
    | ~ spl17_7
    | ~ spl17_11
    | ~ spl17_170 ),
    inference(subsumption_resolution,[],[f10813,f409])).

fof(f10813,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl17_1
    | ~ spl17_4
    | ~ spl17_11
    | ~ spl17_170 ),
    inference(subsumption_resolution,[],[f10812,f238])).

fof(f10812,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl17_1
    | ~ spl17_4
    | ~ spl17_11
    | ~ spl17_170 ),
    inference(subsumption_resolution,[],[f10811,f358])).

fof(f10811,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_11
    | ~ spl17_170 ),
    inference(subsumption_resolution,[],[f10801,f496])).

fof(f496,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl17_11 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl17_11
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).

fof(f10801,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_170 ),
    inference(resolution,[],[f5631,f143])).

fof(f5631,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl17_170 ),
    inference(avatar_component_clause,[],[f5629])).

fof(f5629,plain,
    ( spl17_170
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_170])])).

fof(f5698,plain,
    ( spl17_170
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11
    | ~ spl17_168 ),
    inference(avatar_split_clause,[],[f5697,f5531,f494,f247,f237,f229,f225,f5629])).

fof(f5531,plain,
    ( spl17_168
  <=> r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_168])])).

fof(f5697,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11
    | ~ spl17_168 ),
    inference(forward_demodulation,[],[f5696,f426])).

fof(f5696,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)),k5_lattices(sK0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11
    | ~ spl17_168 ),
    inference(forward_demodulation,[],[f5695,f428])).

fof(f5695,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11
    | ~ spl17_168 ),
    inference(subsumption_resolution,[],[f5622,f496])).

fof(f5622,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_168 ),
    inference(resolution,[],[f5533,f772])).

fof(f772,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f771,f226])).

fof(f771,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f770,f238])).

fof(f770,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(subsumption_resolution,[],[f756,f357])).

fof(f756,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(resolution,[],[f498,f178])).

fof(f498,plain,
    ( ! [X0] : r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6 ),
    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f357,f211])).

fof(f5533,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | ~ spl17_168 ),
    inference(avatar_component_clause,[],[f5531])).

fof(f5534,plain,
    ( spl17_168
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11
    | ~ spl17_140 ),
    inference(avatar_split_clause,[],[f5485,f5264,f494,f247,f237,f229,f225,f5531])).

fof(f5264,plain,
    ( spl17_140
  <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_140])])).

fof(f5485,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11
    | ~ spl17_140 ),
    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f860,f496,f358,f5266,f217])).

fof(f5266,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl17_140 ),
    inference(avatar_component_clause,[],[f5264])).

fof(f5267,plain,
    ( spl17_140
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_13 ),
    inference(avatar_split_clause,[],[f5245,f689,f247,f237,f229,f225,f5264])).

fof(f689,plain,
    ( spl17_13
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_13])])).

fof(f5245,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_13 ),
    inference(superposition,[],[f5120,f691])).

fof(f691,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ spl17_13 ),
    inference(avatar_component_clause,[],[f689])).

fof(f1063,plain,
    ( ~ spl17_3
    | spl17_35
    | spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_11 ),
    inference(avatar_split_clause,[],[f1059,f494,f422,f237,f225,f1061,f233])).

fof(f1059,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ v13_lattices(sK0) )
    | spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_11 ),
    inference(subsumption_resolution,[],[f1058,f226])).

fof(f1058,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_4
    | ~ spl17_10
    | ~ spl17_11 ),
    inference(subsumption_resolution,[],[f1057,f424])).

fof(f1057,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_4
    | ~ spl17_11 ),
    inference(subsumption_resolution,[],[f530,f496])).

fof(f530,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl17_1
    | ~ spl17_4 ),
    inference(resolution,[],[f357,f208])).

fof(f208,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f80,f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
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
    inference(rectify,[],[f79])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f720,plain,
    ( spl17_13
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11 ),
    inference(avatar_split_clause,[],[f719,f494,f247,f237,f229,f225,f689])).

fof(f719,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11 ),
    inference(subsumption_resolution,[],[f718,f226])).

fof(f718,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl17_2
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11 ),
    inference(subsumption_resolution,[],[f717,f230])).

fof(f717,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_4
    | ~ spl17_6
    | ~ spl17_11 ),
    inference(subsumption_resolution,[],[f716,f249])).

fof(f716,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_4
    | ~ spl17_11 ),
    inference(subsumption_resolution,[],[f657,f238])).

fof(f657,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl17_11 ),
    inference(resolution,[],[f496,f162])).

fof(f497,plain,
    ( spl17_11
    | spl17_1
    | ~ spl17_10 ),
    inference(avatar_split_clause,[],[f478,f422,f225,f494])).

fof(f478,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl17_1
    | ~ spl17_10 ),
    inference(unit_resulting_resolution,[],[f226,f424,f145])).

fof(f145,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f425,plain,
    ( spl17_10
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f353,f237,f422])).

fof(f353,plain,
    ( l1_lattices(sK0)
    | ~ spl17_4 ),
    inference(unit_resulting_resolution,[],[f238,f137])).

fof(f137,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f420,plain,
    ( spl17_9
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f354,f237,f229,f225,f417])).

fof(f354,plain,
    ( v6_lattices(sK0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4 ),
    inference(unit_resulting_resolution,[],[f226,f230,f238,f139])).

fof(f139,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
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

fof(f415,plain,
    ( spl17_8
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f355,f237,f229,f225,f412])).

fof(f355,plain,
    ( v8_lattices(sK0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4 ),
    inference(unit_resulting_resolution,[],[f226,f230,f238,f140])).

fof(f140,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f410,plain,
    ( spl17_7
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f356,f237,f229,f225,f407])).

fof(f356,plain,
    ( v9_lattices(sK0)
    | spl17_1
    | ~ spl17_2
    | ~ spl17_4 ),
    inference(unit_resulting_resolution,[],[f226,f230,f238,f141])).

fof(f141,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f252,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f131,f225])).

fof(f131,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f76])).

fof(f76,plain,
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
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
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
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

fof(f251,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f132,f229])).

fof(f132,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f250,plain,(
    spl17_6 ),
    inference(avatar_split_clause,[],[f133,f247])).

fof(f133,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f245,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f134,f237])).

fof(f134,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f244,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | ~ spl17_4
    | ~ spl17_5 ),
    inference(avatar_split_clause,[],[f135,f241,f237,f233,f229,f225])).

fof(f135,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (9183)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (9208)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (9180)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (9205)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (9180)Refutation not found, incomplete strategy% (9180)------------------------------
% 0.20/0.51  % (9180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9180)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9180)Memory used [KB]: 1663
% 0.20/0.51  % (9180)Time elapsed: 0.003 s
% 0.20/0.51  % (9180)------------------------------
% 0.20/0.51  % (9180)------------------------------
% 0.20/0.51  % (9185)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (9192)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (9193)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (9188)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (9198)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (9186)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (9182)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (9209)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (9191)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (9191)Refutation not found, incomplete strategy% (9191)------------------------------
% 0.20/0.52  % (9191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9191)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (9191)Memory used [KB]: 10746
% 0.20/0.52  % (9191)Time elapsed: 0.126 s
% 0.20/0.52  % (9191)------------------------------
% 0.20/0.52  % (9191)------------------------------
% 0.20/0.53  % (9184)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (9194)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (9189)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (9204)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (9207)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (9201)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (9181)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (9197)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (9197)Refutation not found, incomplete strategy% (9197)------------------------------
% 0.20/0.54  % (9197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (9197)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (9197)Memory used [KB]: 10618
% 0.20/0.54  % (9197)Time elapsed: 0.129 s
% 0.20/0.54  % (9197)------------------------------
% 0.20/0.54  % (9197)------------------------------
% 0.20/0.54  % (9200)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (9203)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (9196)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (9199)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (9206)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (9190)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (9202)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (9190)Refutation not found, incomplete strategy% (9190)------------------------------
% 0.20/0.55  % (9190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (9195)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (9189)Refutation not found, incomplete strategy% (9189)------------------------------
% 0.20/0.56  % (9189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (9189)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (9189)Memory used [KB]: 10618
% 0.20/0.56  % (9189)Time elapsed: 0.002 s
% 0.20/0.56  % (9189)------------------------------
% 0.20/0.56  % (9189)------------------------------
% 0.20/0.56  % (9187)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (9202)Refutation not found, incomplete strategy% (9202)------------------------------
% 0.20/0.56  % (9202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (9202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (9202)Memory used [KB]: 10874
% 0.20/0.57  % (9202)Time elapsed: 0.078 s
% 0.20/0.57  % (9202)------------------------------
% 0.20/0.57  % (9202)------------------------------
% 0.20/0.57  % (9190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (9190)Memory used [KB]: 10746
% 0.20/0.57  % (9190)Time elapsed: 0.151 s
% 0.20/0.57  % (9190)------------------------------
% 0.20/0.57  % (9190)------------------------------
% 2.12/0.65  % (9235)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.12/0.69  % (9232)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.70  % (9231)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.70  % (9233)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.55/0.71  % (9231)Refutation not found, incomplete strategy% (9231)------------------------------
% 2.55/0.71  % (9231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.71  % (9231)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.71  
% 2.55/0.71  % (9231)Memory used [KB]: 6268
% 2.55/0.71  % (9231)Time elapsed: 0.085 s
% 2.55/0.71  % (9231)------------------------------
% 2.55/0.71  % (9231)------------------------------
% 2.55/0.73  % (9234)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.55/0.75  % (9236)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.91/0.84  % (9185)Time limit reached!
% 2.91/0.84  % (9185)------------------------------
% 2.91/0.84  % (9185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.91/0.84  % (9185)Termination reason: Time limit
% 2.91/0.84  % (9185)Termination phase: Saturation
% 2.91/0.84  
% 2.91/0.84  % (9185)Memory used [KB]: 8827
% 2.91/0.84  % (9185)Time elapsed: 0.400 s
% 2.91/0.84  % (9185)------------------------------
% 2.91/0.84  % (9185)------------------------------
% 3.55/0.88  % (9237)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.82/0.91  % (9192)Time limit reached!
% 3.82/0.91  % (9192)------------------------------
% 3.82/0.91  % (9192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.91  % (9192)Termination reason: Time limit
% 3.82/0.91  % (9192)Termination phase: Saturation
% 3.82/0.91  
% 3.82/0.91  % (9192)Memory used [KB]: 9722
% 3.82/0.91  % (9192)Time elapsed: 0.500 s
% 3.82/0.91  % (9192)------------------------------
% 3.82/0.91  % (9192)------------------------------
% 3.82/0.92  % (9181)Time limit reached!
% 3.82/0.92  % (9181)------------------------------
% 3.82/0.92  % (9181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.82/0.92  % (9181)Termination reason: Time limit
% 3.82/0.92  
% 3.82/0.92  % (9181)Memory used [KB]: 8571
% 3.82/0.92  % (9181)Time elapsed: 0.506 s
% 3.82/0.92  % (9181)------------------------------
% 3.82/0.92  % (9181)------------------------------
% 4.14/0.96  % (9238)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.47/1.01  % (9234)Time limit reached!
% 4.47/1.01  % (9234)------------------------------
% 4.47/1.01  % (9234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.01  % (9234)Termination reason: Time limit
% 4.47/1.01  % (9234)Termination phase: Saturation
% 4.47/1.01  
% 4.47/1.01  % (9234)Memory used [KB]: 7291
% 4.47/1.01  % (9234)Time elapsed: 0.400 s
% 4.47/1.01  % (9234)------------------------------
% 4.47/1.01  % (9234)------------------------------
% 4.47/1.02  % (9196)Time limit reached!
% 4.47/1.02  % (9196)------------------------------
% 4.47/1.02  % (9196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.02  % (9196)Termination reason: Time limit
% 4.47/1.02  % (9196)Termination phase: Saturation
% 4.47/1.02  
% 4.47/1.02  % (9196)Memory used [KB]: 16630
% 4.47/1.02  % (9196)Time elapsed: 0.600 s
% 4.47/1.02  % (9196)------------------------------
% 4.47/1.02  % (9196)------------------------------
% 4.47/1.02  % (9235)Time limit reached!
% 4.47/1.02  % (9235)------------------------------
% 4.47/1.02  % (9235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.02  % (9235)Termination reason: Time limit
% 4.47/1.02  
% 4.47/1.02  % (9235)Memory used [KB]: 14967
% 4.47/1.02  % (9235)Time elapsed: 0.425 s
% 4.47/1.02  % (9235)------------------------------
% 4.47/1.02  % (9235)------------------------------
% 4.47/1.02  % (9208)Time limit reached!
% 4.47/1.02  % (9208)------------------------------
% 4.47/1.02  % (9208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.02  % (9208)Termination reason: Time limit
% 4.47/1.02  
% 4.47/1.02  % (9208)Memory used [KB]: 8443
% 4.47/1.02  % (9208)Time elapsed: 0.616 s
% 4.47/1.02  % (9208)------------------------------
% 4.47/1.02  % (9208)------------------------------
% 4.47/1.04  % (9239)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.47/1.04  % (9240)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.47/1.06  % (9187)Time limit reached!
% 4.47/1.06  % (9187)------------------------------
% 4.47/1.06  % (9187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.06  % (9187)Termination reason: Time limit
% 4.47/1.06  
% 4.47/1.06  % (9187)Memory used [KB]: 10490
% 4.47/1.06  % (9187)Time elapsed: 0.608 s
% 4.47/1.06  % (9187)------------------------------
% 4.47/1.06  % (9187)------------------------------
% 6.34/1.18  % (9243)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.34/1.18  % (9241)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.34/1.18  % (9242)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.61/1.20  % (9244)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.61/1.23  % (9201)Time limit reached!
% 6.61/1.23  % (9201)------------------------------
% 6.61/1.23  % (9201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.61/1.23  % (9201)Termination reason: Time limit
% 6.61/1.23  % (9201)Termination phase: Saturation
% 6.61/1.23  
% 6.61/1.23  % (9201)Memory used [KB]: 4861
% 6.61/1.23  % (9201)Time elapsed: 0.834 s
% 6.61/1.23  % (9201)------------------------------
% 6.61/1.23  % (9201)------------------------------
% 6.86/1.24  % (9245)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 8.00/1.40  % (9182)Time limit reached!
% 8.00/1.40  % (9182)------------------------------
% 8.00/1.40  % (9182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.00/1.40  % (9182)Termination reason: Time limit
% 8.00/1.40  % (9182)Termination phase: Saturation
% 8.00/1.40  
% 8.00/1.40  % (9182)Memory used [KB]: 25330
% 8.00/1.40  % (9182)Time elapsed: 1.0000 s
% 8.00/1.40  % (9182)------------------------------
% 8.00/1.40  % (9182)------------------------------
% 8.00/1.42  % (9246)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 8.83/1.53  % (9247)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 9.08/1.55  % (9243)Time limit reached!
% 9.08/1.55  % (9243)------------------------------
% 9.08/1.55  % (9243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.08/1.55  % (9243)Termination reason: Time limit
% 9.08/1.55  % (9243)Termination phase: Saturation
% 9.08/1.55  
% 9.08/1.55  % (9243)Memory used [KB]: 2430
% 9.08/1.55  % (9243)Time elapsed: 0.507 s
% 9.08/1.55  % (9243)------------------------------
% 9.08/1.55  % (9243)------------------------------
% 9.08/1.62  % (9206)Time limit reached!
% 9.08/1.62  % (9206)------------------------------
% 9.08/1.62  % (9206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.08/1.62  % (9206)Termination reason: Time limit
% 9.08/1.62  
% 9.08/1.62  % (9206)Memory used [KB]: 18805
% 9.08/1.62  % (9206)Time elapsed: 1.221 s
% 9.08/1.62  % (9206)------------------------------
% 9.08/1.62  % (9206)------------------------------
% 9.76/1.69  % (9248)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 9.76/1.69  % (9248)Refutation not found, incomplete strategy% (9248)------------------------------
% 9.76/1.69  % (9248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.76/1.69  % (9248)Termination reason: Refutation not found, incomplete strategy
% 9.76/1.69  
% 9.76/1.69  % (9248)Memory used [KB]: 6268
% 9.76/1.69  % (9248)Time elapsed: 0.120 s
% 9.76/1.69  % (9248)------------------------------
% 9.76/1.69  % (9248)------------------------------
% 10.59/1.74  % (9205)Refutation found. Thanks to Tanya!
% 10.59/1.74  % SZS status Theorem for theBenchmark
% 10.59/1.74  % SZS output start Proof for theBenchmark
% 10.59/1.74  fof(f21222,plain,(
% 10.59/1.74    $false),
% 10.59/1.74    inference(avatar_sat_refutation,[],[f244,f245,f250,f251,f252,f410,f415,f420,f425,f497,f720,f1063,f5267,f5534,f5698,f10819,f21221])).
% 10.59/1.74  fof(f21221,plain,(
% 10.59/1.74    spl17_1 | ~spl17_2 | spl17_3 | ~spl17_4 | ~spl17_6 | ~spl17_7 | ~spl17_8 | ~spl17_9 | ~spl17_10),
% 10.59/1.74    inference(avatar_contradiction_clause,[],[f21220])).
% 10.59/1.74  fof(f21220,plain,(
% 10.59/1.74    $false | (spl17_1 | ~spl17_2 | spl17_3 | ~spl17_4 | ~spl17_6 | ~spl17_7 | ~spl17_8 | ~spl17_9 | ~spl17_10)),
% 10.59/1.74    inference(subsumption_resolution,[],[f21189,f567])).
% 10.59/1.74  fof(f567,plain,(
% 10.59/1.74    ( ! [X0] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) ) | (spl17_1 | spl17_3 | ~spl17_4 | ~spl17_10)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f424,f235,f358,f153])).
% 10.59/1.74  fof(f153,plain,(
% 10.59/1.74    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f87])).
% 10.59/1.74  fof(f87,plain,(
% 10.59/1.74    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f84,f86,f85])).
% 10.59/1.74  fof(f85,plain,(
% 10.59/1.74    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f86,plain,(
% 10.59/1.74    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f84,plain,(
% 10.59/1.74    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(rectify,[],[f83])).
% 10.59/1.74  fof(f83,plain,(
% 10.59/1.74    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(nnf_transformation,[],[f45])).
% 10.59/1.74  fof(f45,plain,(
% 10.59/1.74    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f44])).
% 10.59/1.74  fof(f44,plain,(
% 10.59/1.74    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f11])).
% 10.59/1.74  fof(f11,axiom,(
% 10.59/1.74    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 10.59/1.74  fof(f358,plain,(
% 10.59/1.74    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl17_1 | ~spl17_4)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f238,f183])).
% 10.59/1.74  fof(f183,plain,(
% 10.59/1.74    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f67])).
% 10.59/1.74  fof(f67,plain,(
% 10.59/1.74    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f66])).
% 10.59/1.74  fof(f66,plain,(
% 10.59/1.74    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f15])).
% 10.59/1.74  fof(f15,axiom,(
% 10.59/1.74    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 10.59/1.74  fof(f238,plain,(
% 10.59/1.74    l3_lattices(sK0) | ~spl17_4),
% 10.59/1.74    inference(avatar_component_clause,[],[f237])).
% 10.59/1.74  fof(f237,plain,(
% 10.59/1.74    spl17_4 <=> l3_lattices(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).
% 10.59/1.74  fof(f235,plain,(
% 10.59/1.74    ~v13_lattices(sK0) | spl17_3),
% 10.59/1.74    inference(avatar_component_clause,[],[f233])).
% 10.59/1.74  fof(f233,plain,(
% 10.59/1.74    spl17_3 <=> v13_lattices(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).
% 10.59/1.74  fof(f424,plain,(
% 10.59/1.74    l1_lattices(sK0) | ~spl17_10),
% 10.59/1.74    inference(avatar_component_clause,[],[f422])).
% 10.59/1.74  fof(f422,plain,(
% 10.59/1.74    spl17_10 <=> l1_lattices(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).
% 10.59/1.74  fof(f226,plain,(
% 10.59/1.74    ~v2_struct_0(sK0) | spl17_1),
% 10.59/1.74    inference(avatar_component_clause,[],[f225])).
% 10.59/1.74  fof(f225,plain,(
% 10.59/1.74    spl17_1 <=> v2_struct_0(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).
% 10.59/1.74  fof(f21189,plain,(
% 10.59/1.74    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl17_1 | ~spl17_2 | spl17_3 | ~spl17_4 | ~spl17_6 | ~spl17_7 | ~spl17_8 | ~spl17_9 | ~spl17_10)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f414,f409,f238,f358,f11271,f11815,f143])).
% 10.59/1.74  fof(f143,plain,(
% 10.59/1.74    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f78])).
% 10.59/1.74  fof(f78,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(nnf_transformation,[],[f39])).
% 10.59/1.74  fof(f39,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f38])).
% 10.59/1.74  fof(f38,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f10])).
% 10.59/1.74  fof(f10,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 10.59/1.74  fof(f11815,plain,(
% 10.59/1.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl17_1 | spl17_3 | ~spl17_4 | ~spl17_9 | ~spl17_10)),
% 10.59/1.74    inference(duplicate_literal_removal,[],[f11811])).
% 10.59/1.74  fof(f11811,plain,(
% 10.59/1.74    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl17_1 | spl17_3 | ~spl17_4 | ~spl17_9 | ~spl17_10)),
% 10.59/1.74    inference(superposition,[],[f619,f1391])).
% 10.59/1.74  fof(f1391,plain,(
% 10.59/1.74    ( ! [X0,X1] : (k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))) ) | (spl17_1 | spl17_3 | ~spl17_4 | ~spl17_9 | ~spl17_10)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f424,f419,f358,f567,f155])).
% 10.59/1.74  fof(f155,plain,(
% 10.59/1.74    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f92])).
% 10.59/1.74  fof(f92,plain,(
% 10.59/1.74    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f89,f91,f90])).
% 10.59/1.74  fof(f90,plain,(
% 10.59/1.74    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f91,plain,(
% 10.59/1.74    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f89,plain,(
% 10.59/1.74    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(rectify,[],[f88])).
% 10.59/1.74  fof(f88,plain,(
% 10.59/1.74    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(nnf_transformation,[],[f47])).
% 10.59/1.74  fof(f47,plain,(
% 10.59/1.74    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f46])).
% 10.59/1.74  fof(f46,plain,(
% 10.59/1.74    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f14])).
% 10.59/1.74  fof(f14,axiom,(
% 10.59/1.74    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 10.59/1.74  fof(f419,plain,(
% 10.59/1.74    v6_lattices(sK0) | ~spl17_9),
% 10.59/1.74    inference(avatar_component_clause,[],[f417])).
% 10.59/1.74  fof(f417,plain,(
% 10.59/1.74    spl17_9 <=> v6_lattices(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_9])])).
% 10.59/1.74  fof(f619,plain,(
% 10.59/1.74    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))) ) | (spl17_1 | spl17_3 | ~spl17_4 | ~spl17_10)),
% 10.59/1.74    inference(subsumption_resolution,[],[f618,f226])).
% 10.59/1.74  fof(f618,plain,(
% 10.59/1.74    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | v2_struct_0(sK0)) ) | (spl17_1 | spl17_3 | ~spl17_4 | ~spl17_10)),
% 10.59/1.74    inference(subsumption_resolution,[],[f617,f424])).
% 10.59/1.74  fof(f617,plain,(
% 10.59/1.74    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | spl17_3 | ~spl17_4)),
% 10.59/1.74    inference(subsumption_resolution,[],[f585,f235])).
% 10.59/1.74  fof(f585,plain,(
% 10.59/1.74    ( ! [X16] : (v13_lattices(sK0) | k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_4)),
% 10.59/1.74    inference(resolution,[],[f358,f154])).
% 10.59/1.74  fof(f154,plain,(
% 10.59/1.74    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f87])).
% 10.59/1.74  fof(f11271,plain,(
% 10.59/1.74    ( ! [X4] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X4)))) ) | (spl17_1 | ~spl17_2 | spl17_3 | ~spl17_4 | ~spl17_6 | ~spl17_10)),
% 10.59/1.74    inference(superposition,[],[f8412,f1402])).
% 10.59/1.74  fof(f1402,plain,(
% 10.59/1.74    ( ! [X0] : (sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,k15_lattice3(sK0,X0))))) ) | (spl17_1 | ~spl17_2 | spl17_3 | ~spl17_4 | ~spl17_6 | ~spl17_10)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f567,f162])).
% 10.59/1.74  fof(f162,plain,(
% 10.59/1.74    ( ! [X0,X1] : (k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f53])).
% 10.59/1.74  fof(f53,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f52])).
% 10.59/1.74  fof(f52,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f23])).
% 10.59/1.74  fof(f23,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).
% 10.59/1.74  fof(f249,plain,(
% 10.59/1.74    v4_lattice3(sK0) | ~spl17_6),
% 10.59/1.74    inference(avatar_component_clause,[],[f247])).
% 10.59/1.74  fof(f247,plain,(
% 10.59/1.74    spl17_6 <=> v4_lattice3(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).
% 10.59/1.74  fof(f230,plain,(
% 10.59/1.74    v10_lattices(sK0) | ~spl17_2),
% 10.59/1.74    inference(avatar_component_clause,[],[f229])).
% 10.59/1.74  fof(f229,plain,(
% 10.59/1.74    spl17_2 <=> v10_lattices(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).
% 10.59/1.74  fof(f8412,plain,(
% 10.59/1.74    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f238,f358,f358,f1503,f5229,f178])).
% 10.59/1.74  % (9204)Time limit reached!
% 10.59/1.74  % (9204)------------------------------
% 10.59/1.74  % (9204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.59/1.74  % (9204)Termination reason: Time limit
% 10.59/1.74  
% 10.59/1.74  fof(f178,plain,(
% 10.59/1.74    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f108])).
% 10.59/1.74  % (9204)Memory used [KB]: 20596
% 10.59/1.74  % (9204)Time elapsed: 1.324 s
% 10.59/1.74  % (9204)------------------------------
% 10.59/1.74  % (9204)------------------------------
% 10.59/1.74  fof(f108,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f106,f107])).
% 10.59/1.74  fof(f107,plain,(
% 10.59/1.74    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f106,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(rectify,[],[f105])).
% 10.59/1.74  fof(f105,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(nnf_transformation,[],[f63])).
% 10.59/1.74  fof(f63,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f62])).
% 10.59/1.74  fof(f62,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f12])).
% 10.59/1.74  fof(f12,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 10.59/1.74  fof(f5229,plain,(
% 10.59/1.74    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f860,f358,f358,f5120,f217])).
% 10.59/1.74  fof(f217,plain,(
% 10.59/1.74    ( ! [X4,X2,X3,X1] : (r2_hidden(X3,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 10.59/1.74    inference(equality_resolution,[],[f201])).
% 10.59/1.74  fof(f201,plain,(
% 10.59/1.74    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f125])).
% 10.59/1.74  fof(f125,plain,(
% 10.59/1.74    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK14(X0,X1,X2),X2) & r3_lattices(X1,sK14(X0,X1,X2),sK13(X0,X1,X2)) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))) & sK13(X0,X1,X2) = X0 & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f122,f124,f123])).
% 10.59/1.74  fof(f123,plain,(
% 10.59/1.74    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK13(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) & sK13(X0,X1,X2) = X0 & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f124,plain,(
% 10.59/1.74    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK13(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK14(X0,X1,X2),X2) & r3_lattices(X1,sK14(X0,X1,X2),sK13(X0,X1,X2)) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f122,plain,(
% 10.59/1.74    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(rectify,[],[f121])).
% 10.59/1.74  fof(f121,plain,(
% 10.59/1.74    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(nnf_transformation,[],[f73])).
% 10.59/1.74  fof(f73,plain,(
% 10.59/1.74    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(flattening,[],[f72])).
% 10.59/1.74  fof(f72,plain,(
% 10.59/1.74    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 10.59/1.74    inference(ennf_transformation,[],[f19])).
% 10.59/1.74  fof(f19,axiom,(
% 10.59/1.74    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).
% 10.59/1.74  fof(f5120,plain,(
% 10.59/1.74    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f136,f1808])).
% 10.59/1.74  fof(f1808,plain,(
% 10.59/1.74    ( ! [X14,X15] : (~r1_tarski(X14,sK7(sK0,X14,a_2_5_lattice3(sK0,X15))) | r3_lattices(sK0,k15_lattice3(sK0,X14),k15_lattice3(sK0,X15))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(resolution,[],[f806,f191])).
% 10.59/1.74  fof(f191,plain,(
% 10.59/1.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f69])).
% 10.59/1.74  fof(f69,plain,(
% 10.59/1.74    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 10.59/1.74    inference(ennf_transformation,[],[f5])).
% 10.59/1.74  fof(f5,axiom,(
% 10.59/1.74    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 10.59/1.74  fof(f806,plain,(
% 10.59/1.74    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f805,f226])).
% 10.59/1.74  fof(f805,plain,(
% 10.59/1.74    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f804,f230])).
% 10.59/1.74  fof(f804,plain,(
% 10.59/1.74    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f803,f249])).
% 10.59/1.74  fof(f803,plain,(
% 10.59/1.74    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f780,f238])).
% 10.59/1.74  fof(f780,plain,(
% 10.59/1.74    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(superposition,[],[f171,f427])).
% 10.59/1.74  fof(f427,plain,(
% 10.59/1.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f238,f249,f160])).
% 10.59/1.74  fof(f160,plain,(
% 10.59/1.74    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f51])).
% 10.59/1.74  fof(f51,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f50])).
% 10.59/1.74  fof(f50,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f24])).
% 10.59/1.74  fof(f24,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).
% 10.59/1.74  fof(f171,plain,(
% 10.59/1.74    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK7(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f99])).
% 10.59/1.74  fof(f99,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f59,f98])).
% 10.59/1.74  fof(f98,plain,(
% 10.59/1.74    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f59,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f58])).
% 10.59/1.74  fof(f58,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f25])).
% 10.59/1.74  fof(f25,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).
% 10.59/1.74  fof(f136,plain,(
% 10.59/1.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f2])).
% 10.59/1.74  fof(f2,axiom,(
% 10.59/1.74    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 10.59/1.74  fof(f860,plain,(
% 10.59/1.74    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f358,f566,f216])).
% 10.59/1.74  fof(f216,plain,(
% 10.59/1.74    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 10.59/1.74    inference(equality_resolution,[],[f195])).
% 10.59/1.74  fof(f195,plain,(
% 10.59/1.74    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f120])).
% 10.59/1.74  fof(f120,plain,(
% 10.59/1.74    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK12(X0,X1,X2),X2) & sK12(X0,X1,X2) = X0 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f118,f119])).
% 10.59/1.74  fof(f119,plain,(
% 10.59/1.74    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK12(X0,X1,X2),X2) & sK12(X0,X1,X2) = X0 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f118,plain,(
% 10.59/1.74    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(rectify,[],[f117])).
% 10.59/1.74  fof(f117,plain,(
% 10.59/1.74    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(nnf_transformation,[],[f71])).
% 10.59/1.74  fof(f71,plain,(
% 10.59/1.74    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 10.59/1.74    inference(flattening,[],[f70])).
% 10.59/1.74  fof(f70,plain,(
% 10.59/1.74    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 10.59/1.74    inference(ennf_transformation,[],[f17])).
% 10.59/1.74  fof(f17,axiom,(
% 10.59/1.74    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 10.59/1.74  fof(f566,plain,(
% 10.59/1.74    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f358,f223])).
% 10.59/1.74  fof(f223,plain,(
% 10.59/1.74    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(duplicate_literal_removal,[],[f213])).
% 10.59/1.74  fof(f213,plain,(
% 10.59/1.74    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(equality_resolution,[],[f173])).
% 10.59/1.74  fof(f173,plain,(
% 10.59/1.74    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f104])).
% 10.59/1.74  fof(f104,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f102,f103])).
% 10.59/1.74  fof(f103,plain,(
% 10.59/1.74    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f102,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(rectify,[],[f101])).
% 10.59/1.74  fof(f101,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f100])).
% 10.59/1.74  fof(f100,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(nnf_transformation,[],[f61])).
% 10.59/1.74  fof(f61,plain,(
% 10.59/1.74    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f60])).
% 10.59/1.74  fof(f60,plain,(
% 10.59/1.74    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f13])).
% 10.59/1.74  fof(f13,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 10.59/1.74  fof(f1503,plain,(
% 10.59/1.74    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0)))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(superposition,[],[f859,f426])).
% 10.59/1.74  fof(f426,plain,(
% 10.59/1.74    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f238,f249,f159])).
% 10.59/1.74  fof(f159,plain,(
% 10.59/1.74    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f49])).
% 10.59/1.74  fof(f49,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f48])).
% 10.59/1.74  fof(f48,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f21])).
% 10.59/1.74  fof(f21,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 10.59/1.74  fof(f859,plain,(
% 10.59/1.74    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f858,f226])).
% 10.59/1.74  fof(f858,plain,(
% 10.59/1.74    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f857,f230])).
% 10.59/1.74  fof(f857,plain,(
% 10.59/1.74    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f856,f249])).
% 10.59/1.74  fof(f856,plain,(
% 10.59/1.74    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f855,f238])).
% 10.59/1.74  fof(f855,plain,(
% 10.59/1.74    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f844,f357])).
% 10.59/1.74  fof(f357,plain,(
% 10.59/1.74    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl17_1 | ~spl17_4)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f238,f182])).
% 10.59/1.74  fof(f182,plain,(
% 10.59/1.74    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f65])).
% 10.59/1.74  fof(f65,plain,(
% 10.59/1.74    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f64])).
% 10.59/1.74  fof(f64,plain,(
% 10.59/1.74    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f16])).
% 10.59/1.74  fof(f16,axiom,(
% 10.59/1.74    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 10.59/1.74  fof(f844,plain,(
% 10.59/1.74    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~m1_subset_1(k16_lattice3(sK0,X17),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(superposition,[],[f211,f428])).
% 10.59/1.74  fof(f428,plain,(
% 10.59/1.74    ( ! [X0] : (k16_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f238,f249,f161])).
% 10.59/1.74  fof(f161,plain,(
% 10.59/1.74    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f51])).
% 10.59/1.74  fof(f211,plain,(
% 10.59/1.74    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(equality_resolution,[],[f165])).
% 10.59/1.74  fof(f165,plain,(
% 10.59/1.74    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.74    inference(cnf_transformation,[],[f97])).
% 10.59/1.74  fof(f97,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f95,f96])).
% 10.59/1.74  fof(f96,plain,(
% 10.59/1.74    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 10.59/1.74    introduced(choice_axiom,[])).
% 10.59/1.74  fof(f95,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(rectify,[],[f94])).
% 10.59/1.74  fof(f94,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f93])).
% 10.59/1.74  fof(f93,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(nnf_transformation,[],[f57])).
% 10.59/1.74  fof(f57,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.74    inference(flattening,[],[f56])).
% 10.59/1.74  fof(f56,plain,(
% 10.59/1.74    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.74    inference(ennf_transformation,[],[f20])).
% 10.59/1.74  fof(f20,axiom,(
% 10.59/1.74    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 10.59/1.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 10.59/1.74  fof(f409,plain,(
% 10.59/1.74    v9_lattices(sK0) | ~spl17_7),
% 10.59/1.74    inference(avatar_component_clause,[],[f407])).
% 10.59/1.74  fof(f407,plain,(
% 10.59/1.74    spl17_7 <=> v9_lattices(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).
% 10.59/1.74  fof(f414,plain,(
% 10.59/1.74    v8_lattices(sK0) | ~spl17_8),
% 10.59/1.74    inference(avatar_component_clause,[],[f412])).
% 10.59/1.74  fof(f412,plain,(
% 10.59/1.74    spl17_8 <=> v8_lattices(sK0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).
% 10.59/1.74  fof(f10819,plain,(
% 10.59/1.74    spl17_1 | ~spl17_2 | ~spl17_4 | spl17_5 | ~spl17_6 | ~spl17_7 | ~spl17_8 | ~spl17_11 | ~spl17_35 | ~spl17_170),
% 10.59/1.74    inference(avatar_contradiction_clause,[],[f10818])).
% 10.59/1.74  fof(f10818,plain,(
% 10.59/1.74    $false | (spl17_1 | ~spl17_2 | ~spl17_4 | spl17_5 | ~spl17_6 | ~spl17_7 | ~spl17_8 | ~spl17_11 | ~spl17_35 | ~spl17_170)),
% 10.59/1.74    inference(subsumption_resolution,[],[f10817,f243])).
% 10.59/1.74  fof(f243,plain,(
% 10.59/1.74    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl17_5),
% 10.59/1.74    inference(avatar_component_clause,[],[f241])).
% 10.59/1.74  fof(f241,plain,(
% 10.59/1.74    spl17_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).
% 10.59/1.74  fof(f10817,plain,(
% 10.59/1.74    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_7 | ~spl17_8 | ~spl17_11 | ~spl17_35 | ~spl17_170)),
% 10.59/1.74    inference(forward_demodulation,[],[f10816,f3079])).
% 10.59/1.74  fof(f3079,plain,(
% 10.59/1.74    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_35)),
% 10.59/1.74    inference(superposition,[],[f1062,f426])).
% 10.59/1.74  fof(f1062,plain,(
% 10.59/1.74    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))) ) | ~spl17_35),
% 10.59/1.74    inference(avatar_component_clause,[],[f1061])).
% 10.59/1.74  fof(f1061,plain,(
% 10.59/1.74    spl17_35 <=> ! [X44] : k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_35])])).
% 10.59/1.74  fof(f10816,plain,(
% 10.59/1.74    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl17_1 | ~spl17_4 | ~spl17_7 | ~spl17_8 | ~spl17_11 | ~spl17_170)),
% 10.59/1.74    inference(subsumption_resolution,[],[f10815,f226])).
% 10.59/1.74  fof(f10815,plain,(
% 10.59/1.74    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (spl17_1 | ~spl17_4 | ~spl17_7 | ~spl17_8 | ~spl17_11 | ~spl17_170)),
% 10.59/1.74    inference(subsumption_resolution,[],[f10814,f414])).
% 10.59/1.74  fof(f10814,plain,(
% 10.59/1.74    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl17_1 | ~spl17_4 | ~spl17_7 | ~spl17_11 | ~spl17_170)),
% 10.59/1.74    inference(subsumption_resolution,[],[f10813,f409])).
% 10.59/1.74  fof(f10813,plain,(
% 10.59/1.74    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl17_1 | ~spl17_4 | ~spl17_11 | ~spl17_170)),
% 10.59/1.74    inference(subsumption_resolution,[],[f10812,f238])).
% 10.59/1.74  fof(f10812,plain,(
% 10.59/1.74    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl17_1 | ~spl17_4 | ~spl17_11 | ~spl17_170)),
% 10.59/1.74    inference(subsumption_resolution,[],[f10811,f358])).
% 10.59/1.74  fof(f10811,plain,(
% 10.59/1.74    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl17_11 | ~spl17_170)),
% 10.59/1.74    inference(subsumption_resolution,[],[f10801,f496])).
% 10.59/1.74  fof(f496,plain,(
% 10.59/1.74    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl17_11),
% 10.59/1.74    inference(avatar_component_clause,[],[f494])).
% 10.59/1.74  fof(f494,plain,(
% 10.59/1.74    spl17_11 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).
% 10.59/1.74  fof(f10801,plain,(
% 10.59/1.74    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | ~spl17_170),
% 10.59/1.74    inference(resolution,[],[f5631,f143])).
% 10.59/1.74  fof(f5631,plain,(
% 10.59/1.74    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl17_170),
% 10.59/1.74    inference(avatar_component_clause,[],[f5629])).
% 10.59/1.74  fof(f5629,plain,(
% 10.59/1.74    spl17_170 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_170])])).
% 10.59/1.74  fof(f5698,plain,(
% 10.59/1.74    spl17_170 | spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11 | ~spl17_168),
% 10.59/1.74    inference(avatar_split_clause,[],[f5697,f5531,f494,f247,f237,f229,f225,f5629])).
% 10.59/1.74  fof(f5531,plain,(
% 10.59/1.74    spl17_168 <=> r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_168])])).
% 10.59/1.74  fof(f5697,plain,(
% 10.59/1.74    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11 | ~spl17_168)),
% 10.59/1.74    inference(forward_demodulation,[],[f5696,f426])).
% 10.59/1.74  fof(f5696,plain,(
% 10.59/1.74    r1_lattices(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)),k5_lattices(sK0)) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11 | ~spl17_168)),
% 10.59/1.74    inference(forward_demodulation,[],[f5695,f428])).
% 10.59/1.74  fof(f5695,plain,(
% 10.59/1.74    r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0)) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11 | ~spl17_168)),
% 10.59/1.74    inference(subsumption_resolution,[],[f5622,f496])).
% 10.59/1.74  fof(f5622,plain,(
% 10.59/1.74    r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_168)),
% 10.59/1.74    inference(resolution,[],[f5533,f772])).
% 10.59/1.74  fof(f772,plain,(
% 10.59/1.74    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f771,f226])).
% 10.59/1.74  fof(f771,plain,(
% 10.59/1.74    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f770,f238])).
% 10.59/1.74  fof(f770,plain,(
% 10.59/1.74    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(subsumption_resolution,[],[f756,f357])).
% 10.59/1.74  fof(f756,plain,(
% 10.59/1.74    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(resolution,[],[f498,f178])).
% 10.59/1.74  fof(f498,plain,(
% 10.59/1.74    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)) ) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f357,f211])).
% 10.59/1.74  fof(f5533,plain,(
% 10.59/1.74    r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) | ~spl17_168),
% 10.59/1.74    inference(avatar_component_clause,[],[f5531])).
% 10.59/1.74  fof(f5534,plain,(
% 10.59/1.74    spl17_168 | spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11 | ~spl17_140),
% 10.59/1.74    inference(avatar_split_clause,[],[f5485,f5264,f494,f247,f237,f229,f225,f5531])).
% 10.59/1.74  fof(f5264,plain,(
% 10.59/1.74    spl17_140 <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_140])])).
% 10.59/1.74  fof(f5485,plain,(
% 10.59/1.74    r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11 | ~spl17_140)),
% 10.59/1.74    inference(unit_resulting_resolution,[],[f226,f230,f249,f238,f860,f496,f358,f5266,f217])).
% 10.59/1.74  fof(f5266,plain,(
% 10.59/1.74    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl17_140),
% 10.59/1.74    inference(avatar_component_clause,[],[f5264])).
% 10.59/1.74  fof(f5267,plain,(
% 10.59/1.74    spl17_140 | spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_13),
% 10.59/1.74    inference(avatar_split_clause,[],[f5245,f689,f247,f237,f229,f225,f5264])).
% 10.59/1.74  fof(f689,plain,(
% 10.59/1.74    spl17_13 <=> k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))),
% 10.59/1.74    introduced(avatar_definition,[new_symbols(naming,[spl17_13])])).
% 10.59/1.74  fof(f5245,plain,(
% 10.59/1.74    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_13)),
% 10.59/1.74    inference(superposition,[],[f5120,f691])).
% 10.59/1.74  fof(f691,plain,(
% 10.59/1.74    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~spl17_13),
% 10.59/1.74    inference(avatar_component_clause,[],[f689])).
% 10.59/1.74  fof(f1063,plain,(
% 10.59/1.74    ~spl17_3 | spl17_35 | spl17_1 | ~spl17_4 | ~spl17_10 | ~spl17_11),
% 10.59/1.74    inference(avatar_split_clause,[],[f1059,f494,f422,f237,f225,f1061,f233])).
% 10.59/1.74  fof(f1059,plain,(
% 10.59/1.74    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0)) ) | (spl17_1 | ~spl17_4 | ~spl17_10 | ~spl17_11)),
% 10.59/1.74    inference(subsumption_resolution,[],[f1058,f226])).
% 10.59/1.75  fof(f1058,plain,(
% 10.59/1.75    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_4 | ~spl17_10 | ~spl17_11)),
% 10.59/1.75    inference(subsumption_resolution,[],[f1057,f424])).
% 10.59/1.75  fof(f1057,plain,(
% 10.59/1.75    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_4 | ~spl17_11)),
% 10.59/1.75    inference(subsumption_resolution,[],[f530,f496])).
% 10.59/1.75  fof(f530,plain,(
% 10.59/1.75    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl17_1 | ~spl17_4)),
% 10.59/1.75    inference(resolution,[],[f357,f208])).
% 10.59/1.75  fof(f208,plain,(
% 10.59/1.75    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.75    inference(equality_resolution,[],[f147])).
% 10.59/1.75  fof(f147,plain,(
% 10.59/1.75    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.75    inference(cnf_transformation,[],[f82])).
% 10.59/1.75  fof(f82,plain,(
% 10.59/1.75    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f80,f81])).
% 10.59/1.75  fof(f81,plain,(
% 10.59/1.75    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 10.59/1.75    introduced(choice_axiom,[])).
% 10.59/1.75  fof(f80,plain,(
% 10.59/1.75    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.75    inference(rectify,[],[f79])).
% 10.59/1.75  fof(f79,plain,(
% 10.59/1.75    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.75    inference(nnf_transformation,[],[f43])).
% 10.59/1.75  fof(f43,plain,(
% 10.59/1.75    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.75    inference(flattening,[],[f42])).
% 10.59/1.77  fof(f42,plain,(
% 10.59/1.77    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.77    inference(ennf_transformation,[],[f7])).
% 10.59/1.77  fof(f7,axiom,(
% 10.59/1.77    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 10.59/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 10.59/1.77  fof(f720,plain,(
% 10.59/1.77    spl17_13 | spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11),
% 10.59/1.77    inference(avatar_split_clause,[],[f719,f494,f247,f237,f229,f225,f689])).
% 10.59/1.77  fof(f719,plain,(
% 10.59/1.77    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | (spl17_1 | ~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11)),
% 10.59/1.77    inference(subsumption_resolution,[],[f718,f226])).
% 10.59/1.77  fof(f718,plain,(
% 10.59/1.77    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl17_2 | ~spl17_4 | ~spl17_6 | ~spl17_11)),
% 10.59/1.77    inference(subsumption_resolution,[],[f717,f230])).
% 10.59/1.77  fof(f717,plain,(
% 10.59/1.77    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl17_4 | ~spl17_6 | ~spl17_11)),
% 10.59/1.77    inference(subsumption_resolution,[],[f716,f249])).
% 10.59/1.77  fof(f716,plain,(
% 10.59/1.77    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl17_4 | ~spl17_11)),
% 10.59/1.77    inference(subsumption_resolution,[],[f657,f238])).
% 10.59/1.77  fof(f657,plain,(
% 10.59/1.77    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl17_11),
% 10.59/1.77    inference(resolution,[],[f496,f162])).
% 10.59/1.77  fof(f497,plain,(
% 10.59/1.77    spl17_11 | spl17_1 | ~spl17_10),
% 10.59/1.77    inference(avatar_split_clause,[],[f478,f422,f225,f494])).
% 10.59/1.77  fof(f478,plain,(
% 10.59/1.77    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl17_1 | ~spl17_10)),
% 10.59/1.77    inference(unit_resulting_resolution,[],[f226,f424,f145])).
% 10.59/1.77  fof(f145,plain,(
% 10.59/1.77    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 10.59/1.77    inference(cnf_transformation,[],[f41])).
% 10.59/1.77  fof(f41,plain,(
% 10.59/1.77    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 10.59/1.77    inference(flattening,[],[f40])).
% 10.59/1.77  fof(f40,plain,(
% 10.59/1.77    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 10.59/1.77    inference(ennf_transformation,[],[f8])).
% 10.59/1.77  fof(f8,axiom,(
% 10.59/1.77    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 10.59/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 10.59/1.77  fof(f425,plain,(
% 10.59/1.77    spl17_10 | ~spl17_4),
% 10.59/1.77    inference(avatar_split_clause,[],[f353,f237,f422])).
% 10.59/1.77  fof(f353,plain,(
% 10.59/1.77    l1_lattices(sK0) | ~spl17_4),
% 10.59/1.77    inference(unit_resulting_resolution,[],[f238,f137])).
% 10.59/1.77  fof(f137,plain,(
% 10.59/1.77    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 10.59/1.77    inference(cnf_transformation,[],[f34])).
% 10.59/1.77  fof(f34,plain,(
% 10.59/1.77    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 10.59/1.77    inference(ennf_transformation,[],[f28])).
% 10.59/1.77  fof(f28,plain,(
% 10.59/1.77    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 10.59/1.77    inference(pure_predicate_removal,[],[f9])).
% 10.59/1.77  fof(f9,axiom,(
% 10.59/1.77    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 10.59/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 10.59/1.77  fof(f420,plain,(
% 10.59/1.77    spl17_9 | spl17_1 | ~spl17_2 | ~spl17_4),
% 10.59/1.77    inference(avatar_split_clause,[],[f354,f237,f229,f225,f417])).
% 10.59/1.77  fof(f354,plain,(
% 10.59/1.77    v6_lattices(sK0) | (spl17_1 | ~spl17_2 | ~spl17_4)),
% 10.59/1.77    inference(unit_resulting_resolution,[],[f226,f230,f238,f139])).
% 10.59/1.77  fof(f139,plain,(
% 10.59/1.77    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 10.59/1.77    inference(cnf_transformation,[],[f36])).
% 10.59/1.77  fof(f36,plain,(
% 10.59/1.77    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 10.59/1.77    inference(flattening,[],[f35])).
% 10.59/1.77  fof(f35,plain,(
% 10.59/1.77    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 10.59/1.77    inference(ennf_transformation,[],[f31])).
% 10.59/1.77  fof(f31,plain,(
% 10.59/1.77    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 10.59/1.77    inference(pure_predicate_removal,[],[f30])).
% 10.59/1.77  fof(f30,plain,(
% 10.59/1.77    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 10.59/1.77    inference(pure_predicate_removal,[],[f29])).
% 10.59/1.77  fof(f29,plain,(
% 10.59/1.77    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 10.59/1.77    inference(pure_predicate_removal,[],[f6])).
% 10.59/1.77  fof(f6,axiom,(
% 10.59/1.77    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 10.59/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 10.59/1.77  fof(f415,plain,(
% 10.59/1.77    spl17_8 | spl17_1 | ~spl17_2 | ~spl17_4),
% 10.59/1.77    inference(avatar_split_clause,[],[f355,f237,f229,f225,f412])).
% 10.59/1.77  fof(f355,plain,(
% 10.59/1.77    v8_lattices(sK0) | (spl17_1 | ~spl17_2 | ~spl17_4)),
% 10.59/1.77    inference(unit_resulting_resolution,[],[f226,f230,f238,f140])).
% 10.59/1.77  fof(f140,plain,(
% 10.59/1.77    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 10.59/1.77    inference(cnf_transformation,[],[f36])).
% 10.59/1.77  fof(f410,plain,(
% 10.59/1.77    spl17_7 | spl17_1 | ~spl17_2 | ~spl17_4),
% 10.59/1.77    inference(avatar_split_clause,[],[f356,f237,f229,f225,f407])).
% 10.59/1.77  fof(f356,plain,(
% 10.59/1.77    v9_lattices(sK0) | (spl17_1 | ~spl17_2 | ~spl17_4)),
% 10.59/1.77    inference(unit_resulting_resolution,[],[f226,f230,f238,f141])).
% 10.59/1.77  fof(f141,plain,(
% 10.59/1.77    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 10.59/1.77    inference(cnf_transformation,[],[f36])).
% 10.59/1.77  fof(f252,plain,(
% 10.59/1.77    ~spl17_1),
% 10.59/1.77    inference(avatar_split_clause,[],[f131,f225])).
% 10.59/1.77  fof(f131,plain,(
% 10.59/1.77    ~v2_struct_0(sK0)),
% 10.59/1.77    inference(cnf_transformation,[],[f77])).
% 10.59/1.77  fof(f77,plain,(
% 10.59/1.77    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 10.59/1.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f76])).
% 10.59/1.77  fof(f76,plain,(
% 10.59/1.77    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 10.59/1.77    introduced(choice_axiom,[])).
% 10.59/1.77  fof(f33,plain,(
% 10.59/1.77    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 10.59/1.77    inference(flattening,[],[f32])).
% 10.59/1.77  fof(f32,plain,(
% 10.59/1.77    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 10.59/1.77    inference(ennf_transformation,[],[f27])).
% 10.59/1.77  fof(f27,negated_conjecture,(
% 10.59/1.77    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 10.59/1.77    inference(negated_conjecture,[],[f26])).
% 10.59/1.77  fof(f26,conjecture,(
% 10.59/1.77    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 10.59/1.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 10.59/1.77  fof(f251,plain,(
% 10.59/1.77    spl17_2),
% 10.59/1.77    inference(avatar_split_clause,[],[f132,f229])).
% 10.59/1.77  fof(f132,plain,(
% 10.59/1.77    v10_lattices(sK0)),
% 10.59/1.77    inference(cnf_transformation,[],[f77])).
% 10.59/1.77  fof(f250,plain,(
% 10.59/1.77    spl17_6),
% 10.59/1.77    inference(avatar_split_clause,[],[f133,f247])).
% 10.59/1.77  fof(f133,plain,(
% 10.59/1.77    v4_lattice3(sK0)),
% 10.59/1.77    inference(cnf_transformation,[],[f77])).
% 10.59/1.77  fof(f245,plain,(
% 10.59/1.77    spl17_4),
% 10.59/1.77    inference(avatar_split_clause,[],[f134,f237])).
% 10.59/1.77  fof(f134,plain,(
% 10.59/1.77    l3_lattices(sK0)),
% 10.59/1.77    inference(cnf_transformation,[],[f77])).
% 10.59/1.77  fof(f244,plain,(
% 10.59/1.77    spl17_1 | ~spl17_2 | ~spl17_3 | ~spl17_4 | ~spl17_5),
% 10.59/1.77    inference(avatar_split_clause,[],[f135,f241,f237,f233,f229,f225])).
% 10.59/1.77  fof(f135,plain,(
% 10.59/1.77    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 10.59/1.77    inference(cnf_transformation,[],[f77])).
% 10.59/1.77  % SZS output end Proof for theBenchmark
% 10.59/1.77  % (9205)------------------------------
% 10.59/1.77  % (9205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.59/1.77  % (9205)Termination reason: Refutation
% 10.59/1.77  
% 10.59/1.77  % (9205)Memory used [KB]: 17526
% 10.59/1.77  % (9205)Time elapsed: 1.354 s
% 10.59/1.77  % (9205)------------------------------
% 10.59/1.77  % (9205)------------------------------
% 11.12/1.77  % (9179)Success in time 1.4 s
%------------------------------------------------------------------------------
