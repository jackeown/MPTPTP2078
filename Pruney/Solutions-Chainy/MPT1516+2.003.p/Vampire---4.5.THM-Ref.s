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
% DateTime   : Thu Dec  3 13:15:47 EST 2020

% Result     : Theorem 15.68s
% Output     : Refutation 16.29s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 837 expanded)
%              Number of leaves         :   48 ( 308 expanded)
%              Depth                    :   21
%              Number of atoms          : 1552 (3853 expanded)
%              Number of equality atoms :  196 ( 386 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31877,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f242,f243,f248,f249,f250,f411,f416,f421,f426,f505,f729,f974,f2121,f2287,f2384,f12330,f31876])).

fof(f31876,plain,
    ( spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(avatar_contradiction_clause,[],[f31875])).

fof(f31875,plain,
    ( $false
    | spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f31844,f573])).

fof(f573,plain,
    ( ! [X0] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f224,f425,f233,f358,f151])).

fof(f151,plain,(
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
    | spl16_1
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f224,f236,f182])).

fof(f182,plain,(
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

fof(f236,plain,
    ( l3_lattices(sK0)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl16_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f233,plain,
    ( ~ v13_lattices(sK0)
    | spl16_3 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl16_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f425,plain,
    ( l1_lattices(sK0)
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl16_10
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f224,plain,
    ( ~ v2_struct_0(sK0)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl16_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f31844,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f224,f415,f410,f236,f358,f12606,f14477,f141])).

fof(f141,plain,(
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

fof(f14477,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(duplicate_literal_removal,[],[f14473])).

fof(f14473,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) )
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(superposition,[],[f624,f1509])).

fof(f1509,plain,
    ( ! [X0,X1] : k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f224,f425,f420,f358,f573,f153])).

fof(f153,plain,(
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

fof(f420,plain,
    ( v6_lattices(sK0)
    | ~ spl16_9 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl16_9
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f624,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) )
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f623,f224])).

fof(f623,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | v2_struct_0(sK0) )
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f622,f425])).

fof(f622,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | spl16_3
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f591,f233])).

fof(f591,plain,
    ( ! [X16] :
        ( v13_lattices(sK0)
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4 ),
    inference(resolution,[],[f358,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f12606,plain,
    ( ! [X4] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X4)))
    | spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_10 ),
    inference(superposition,[],[f4324,f1520])).

fof(f1520,plain,
    ( ! [X0] : sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0))))
    | spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f573,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f247,plain,
    ( v4_lattice3(sK0)
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl16_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f228,plain,
    ( v10_lattices(sK0)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl16_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f4324,plain,
    ( ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f224,f236,f358,f358,f1642,f1249,f177])).

fof(f177,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f108])).

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

fof(f1249,plain,
    ( ! [X0] : r2_hidden(k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f358,f430,f358,f787,f215])).

fof(f215,plain,(
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
    inference(equality_resolution,[],[f199])).

fof(f199,plain,(
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
    inference(cnf_transformation,[],[f123])).

fof(f123,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_6_lattice3(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X2)
            & r3_lattices(X1,sK13(X0,X1,X2),sK12(X0,X1,X2))
            & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
            & sK12(X0,X1,X2) = X0
            & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_6_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f120,f122,f121])).

fof(f121,plain,(
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
            & r3_lattices(X1,X6,sK12(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK12(X0,X1,X2) = X0
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,X6,sK12(X0,X1,X2))
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK13(X0,X1,X2),X2)
        & r3_lattices(X1,sK13(X0,X1,X2),sK12(X0,X1,X2))
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f120,plain,(
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
    inference(rectify,[],[f119])).

fof(f119,plain,(
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

fof(f787,plain,
    ( ! [X0] : r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f358,f572,f214])).

fof(f214,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f193])).

fof(f193,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r4_lattice3(X1,X3,X2)
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r4_lattice3(X1,sK11(X0,X1,X2),X2)
            & sK11(X0,X1,X2) = X0
            & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f116,f117])).

fof(f117,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK11(X0,X1,X2),X2)
        & sK11(X0,X1,X2) = X0
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
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
    inference(rectify,[],[f115])).

fof(f115,plain,(
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

fof(f572,plain,
    ( ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f358,f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f172])).

fof(f172,plain,(
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

fof(f430,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f134,f224,f228,f236,f247,f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
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
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).

fof(f134,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1642,plain,
    ( ! [X0] : r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(superposition,[],[f1433,f427])).

fof(f427,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f224,f228,f236,f247,f157])).

fof(f157,plain,(
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

fof(f1433,plain,
    ( ! [X21] : r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f1432,f224])).

fof(f1432,plain,
    ( ! [X21] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21))
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f1431,f228])).

fof(f1431,plain,
    ( ! [X21] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f1430,f247])).

fof(f1430,plain,
    ( ! [X21] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f1429,f236])).

fof(f1429,plain,
    ( ! [X21] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f1410,f357])).

fof(f357,plain,
    ( ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f224,f236,f181])).

fof(f181,plain,(
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

fof(f1410,plain,
    ( ! [X21] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21))
        | ~ m1_subset_1(k16_lattice3(sK0,X21),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(superposition,[],[f209,f429])).

fof(f429,plain,
    ( ! [X0] : k16_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f224,f228,f236,f247,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
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

fof(f209,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f162])).

fof(f162,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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

fof(f410,plain,
    ( v9_lattices(sK0)
    | ~ spl16_7 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl16_7
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f415,plain,
    ( v8_lattices(sK0)
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl16_8
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f12330,plain,
    ( spl16_1
    | ~ spl16_4
    | spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_52 ),
    inference(avatar_contradiction_clause,[],[f12329])).

fof(f12329,plain,
    ( $false
    | spl16_1
    | ~ spl16_4
    | spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_52 ),
    inference(subsumption_resolution,[],[f12328,f241])).

fof(f241,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl16_5 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl16_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f12328,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_29
    | ~ spl16_52 ),
    inference(forward_demodulation,[],[f12327,f973])).

fof(f973,plain,
    ( ! [X42] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0))
    | ~ spl16_29 ),
    inference(avatar_component_clause,[],[f972])).

fof(f972,plain,
    ( spl16_29
  <=> ! [X42] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_29])])).

fof(f12327,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_52 ),
    inference(subsumption_resolution,[],[f12326,f224])).

fof(f12326,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_52 ),
    inference(subsumption_resolution,[],[f12325,f415])).

fof(f12325,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_7
    | ~ spl16_11
    | ~ spl16_52 ),
    inference(subsumption_resolution,[],[f12324,f410])).

fof(f12324,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_11
    | ~ spl16_52 ),
    inference(subsumption_resolution,[],[f12323,f236])).

fof(f12323,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_11
    | ~ spl16_52 ),
    inference(subsumption_resolution,[],[f12322,f358])).

fof(f12322,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_11
    | ~ spl16_52 ),
    inference(subsumption_resolution,[],[f12312,f504])).

fof(f504,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl16_11 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl16_11
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f12312,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_52 ),
    inference(resolution,[],[f2381,f141])).

fof(f2381,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl16_52 ),
    inference(avatar_component_clause,[],[f2379])).

fof(f2379,plain,
    ( spl16_52
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_52])])).

fof(f2384,plain,
    ( spl16_52
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_51 ),
    inference(avatar_split_clause,[],[f2383,f2284,f502,f245,f235,f227,f223,f2379])).

fof(f2284,plain,
    ( spl16_51
  <=> r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_51])])).

fof(f2383,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_51 ),
    inference(forward_demodulation,[],[f2360,f427])).

fof(f2360,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_51 ),
    inference(unit_resulting_resolution,[],[f224,f236,f504,f357,f1433,f2286,f177])).

fof(f2286,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | ~ spl16_51 ),
    inference(avatar_component_clause,[],[f2284])).

fof(f2287,plain,
    ( spl16_51
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_49 ),
    inference(avatar_split_clause,[],[f2274,f2118,f502,f245,f235,f227,f223,f2284])).

fof(f2118,plain,
    ( spl16_49
  <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_49])])).

fof(f2274,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_49 ),
    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f787,f504,f358,f2120,f215])).

fof(f2120,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl16_49 ),
    inference(avatar_component_clause,[],[f2118])).

fof(f2121,plain,
    ( spl16_49
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_12 ),
    inference(avatar_split_clause,[],[f2084,f688,f245,f235,f227,f223,f2118])).

fof(f688,plain,
    ( spl16_12
  <=> k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).

fof(f2084,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_12 ),
    inference(superposition,[],[f1666,f690])).

fof(f690,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl16_12 ),
    inference(avatar_component_clause,[],[f688])).

fof(f1666,plain,
    ( ! [X1] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k16_lattice3(sK0,X1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(superposition,[],[f430,f510])).

fof(f510,plain,
    ( ! [X0] : k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k16_lattice3(sK0,X0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f357,f160])).

fof(f974,plain,
    ( ~ spl16_3
    | spl16_29
    | spl16_1
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(avatar_split_clause,[],[f970,f502,f423,f235,f223,f972,f231])).

fof(f970,plain,
    ( ! [X42] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0))
        | ~ v13_lattices(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f969,f224])).

fof(f969,plain,
    ( ! [X42] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f968,f425])).

fof(f968,plain,
    ( ! [X42] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f605,f504])).

fof(f605,plain,
    ( ! [X42] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4 ),
    inference(resolution,[],[f358,f206])).

fof(f206,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
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

fof(f729,plain,
    ( spl16_12
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(avatar_split_clause,[],[f728,f502,f245,f235,f227,f223,f688])).

fof(f728,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f727,f224])).

fof(f727,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f726,f228])).

fof(f726,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f725,f247])).

fof(f725,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f663,f236])).

fof(f663,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_11 ),
    inference(resolution,[],[f504,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f505,plain,
    ( spl16_11
    | spl16_1
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f486,f423,f223,f502])).

fof(f486,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f224,f425,f143])).

fof(f143,plain,(
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

fof(f426,plain,
    ( spl16_10
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f353,f235,f423])).

fof(f353,plain,
    ( l1_lattices(sK0)
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f236,f135])).

fof(f135,plain,(
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

fof(f421,plain,
    ( spl16_9
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f354,f235,f227,f223,f418])).

fof(f354,plain,
    ( v6_lattices(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f224,f228,f236,f137])).

fof(f137,plain,(
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

fof(f416,plain,
    ( spl16_8
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f355,f235,f227,f223,f413])).

fof(f355,plain,
    ( v8_lattices(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f224,f228,f236,f138])).

fof(f138,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f411,plain,
    ( spl16_7
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f356,f235,f227,f223,f408])).

fof(f356,plain,
    ( v9_lattices(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f224,f228,f236,f139])).

fof(f139,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f250,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f129,f223])).

fof(f129,plain,(
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

fof(f249,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f130,f227])).

fof(f130,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f248,plain,(
    spl16_6 ),
    inference(avatar_split_clause,[],[f131,f245])).

fof(f131,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f243,plain,(
    spl16_4 ),
    inference(avatar_split_clause,[],[f132,f235])).

fof(f132,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f242,plain,
    ( spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(avatar_split_clause,[],[f133,f239,f235,f231,f227,f223])).

fof(f133,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:02:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5379)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (5379)Refutation not found, incomplete strategy% (5379)------------------------------
% 0.21/0.51  % (5379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5372)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (5379)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5379)Memory used [KB]: 10618
% 0.21/0.51  % (5379)Time elapsed: 0.004 s
% 0.21/0.51  % (5379)------------------------------
% 0.21/0.51  % (5379)------------------------------
% 1.17/0.52  % (5374)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.52  % (5386)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.17/0.52  % (5378)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.17/0.52  % (5396)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.17/0.52  % (5392)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.17/0.52  % (5388)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.17/0.53  % (5382)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.53  % (5384)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (5373)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.17/0.53  % (5399)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.17/0.54  % (5375)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.54  % (5370)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (5370)Refutation not found, incomplete strategy% (5370)------------------------------
% 1.36/0.54  % (5370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (5370)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (5370)Memory used [KB]: 1663
% 1.36/0.54  % (5370)Time elapsed: 0.001 s
% 1.36/0.54  % (5370)------------------------------
% 1.36/0.54  % (5370)------------------------------
% 1.36/0.54  % (5371)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (5377)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.54  % (5374)Refutation not found, incomplete strategy% (5374)------------------------------
% 1.36/0.54  % (5374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (5374)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (5374)Memory used [KB]: 6396
% 1.36/0.54  % (5374)Time elapsed: 0.130 s
% 1.36/0.54  % (5374)------------------------------
% 1.36/0.54  % (5374)------------------------------
% 1.36/0.54  % (5394)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.54  % (5395)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.54  % (5398)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (5391)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (5390)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.55  % (5392)Refutation not found, incomplete strategy% (5392)------------------------------
% 1.36/0.55  % (5392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (5392)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (5392)Memory used [KB]: 10874
% 1.36/0.55  % (5392)Time elapsed: 0.104 s
% 1.36/0.55  % (5392)------------------------------
% 1.36/0.55  % (5392)------------------------------
% 1.36/0.55  % (5387)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.55  % (5383)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.55  % (5397)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.55  % (5387)Refutation not found, incomplete strategy% (5387)------------------------------
% 1.36/0.55  % (5387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (5387)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (5387)Memory used [KB]: 10746
% 1.36/0.55  % (5387)Time elapsed: 0.139 s
% 1.36/0.55  % (5387)------------------------------
% 1.36/0.55  % (5387)------------------------------
% 1.36/0.55  % (5393)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.55  % (5380)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.55  % (5389)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (5380)Refutation not found, incomplete strategy% (5380)------------------------------
% 1.36/0.55  % (5380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (5380)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (5380)Memory used [KB]: 10746
% 1.36/0.55  % (5380)Time elapsed: 0.148 s
% 1.36/0.55  % (5380)------------------------------
% 1.36/0.55  % (5380)------------------------------
% 1.36/0.55  % (5381)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.56  % (5381)Refutation not found, incomplete strategy% (5381)------------------------------
% 1.36/0.56  % (5381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (5376)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.56  % (5385)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.56  % (5381)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (5381)Memory used [KB]: 10746
% 1.36/0.56  % (5381)Time elapsed: 0.151 s
% 1.36/0.56  % (5381)------------------------------
% 1.36/0.56  % (5381)------------------------------
% 1.36/0.62  % (5449)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.97/0.65  % (5460)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.97/0.68  % (5462)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.97/0.68  % (5465)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.97/0.69  % (5467)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.97/0.69  % (5471)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.34/0.70  % (5482)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.01/0.83  % (5375)Time limit reached!
% 3.01/0.83  % (5375)------------------------------
% 3.01/0.83  % (5375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.83  % (5375)Termination reason: Time limit
% 3.01/0.83  
% 3.01/0.83  % (5375)Memory used [KB]: 9210
% 3.01/0.83  % (5375)Time elapsed: 0.415 s
% 3.01/0.83  % (5375)------------------------------
% 3.01/0.83  % (5375)------------------------------
% 3.22/0.93  % (5371)Time limit reached!
% 3.22/0.93  % (5371)------------------------------
% 3.22/0.93  % (5371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.94  % (5371)Termination reason: Time limit
% 3.78/0.94  % (5371)Termination phase: Saturation
% 3.78/0.94  
% 3.78/0.94  % (5371)Memory used [KB]: 8443
% 3.78/0.94  % (5371)Time elapsed: 0.500 s
% 3.78/0.94  % (5371)------------------------------
% 3.78/0.94  % (5371)------------------------------
% 3.78/0.95  % (5382)Time limit reached!
% 3.78/0.95  % (5382)------------------------------
% 3.78/0.95  % (5382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.95  % (5382)Termination reason: Time limit
% 3.78/0.95  % (5382)Termination phase: Saturation
% 3.78/0.95  
% 3.78/0.95  % (5382)Memory used [KB]: 11001
% 3.78/0.95  % (5382)Time elapsed: 0.500 s
% 3.78/0.95  % (5382)------------------------------
% 3.78/0.95  % (5382)------------------------------
% 3.78/0.96  % (5587)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.11/1.00  % (5467)Time limit reached!
% 4.11/1.00  % (5467)------------------------------
% 4.11/1.00  % (5467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/1.00  % (5467)Termination reason: Time limit
% 4.11/1.00  % (5467)Termination phase: Saturation
% 4.11/1.00  
% 4.11/1.00  % (5467)Memory used [KB]: 11897
% 4.11/1.00  % (5467)Time elapsed: 0.427 s
% 4.11/1.00  % (5467)------------------------------
% 4.11/1.00  % (5467)------------------------------
% 4.11/1.01  % (5465)Time limit reached!
% 4.11/1.01  % (5465)------------------------------
% 4.11/1.01  % (5465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/1.01  % (5465)Termination reason: Time limit
% 4.11/1.01  % (5465)Termination phase: Saturation
% 4.11/1.01  
% 4.11/1.01  % (5465)Memory used [KB]: 7419
% 4.11/1.01  % (5465)Time elapsed: 0.409 s
% 4.11/1.01  % (5465)------------------------------
% 4.11/1.01  % (5465)------------------------------
% 4.11/1.04  % (5386)Time limit reached!
% 4.11/1.04  % (5386)------------------------------
% 4.11/1.04  % (5386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/1.04  % (5386)Termination reason: Time limit
% 4.11/1.04  
% 4.11/1.04  % (5386)Memory used [KB]: 17654
% 4.11/1.04  % (5386)Time elapsed: 0.623 s
% 4.11/1.04  % (5386)------------------------------
% 4.11/1.04  % (5386)------------------------------
% 4.11/1.04  % (5398)Time limit reached!
% 4.11/1.04  % (5398)------------------------------
% 4.11/1.04  % (5398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/1.04  % (5398)Termination reason: Time limit
% 4.11/1.04  % (5398)Termination phase: Saturation
% 4.11/1.04  
% 4.11/1.04  % (5398)Memory used [KB]: 7803
% 4.11/1.04  % (5398)Time elapsed: 0.629 s
% 4.11/1.04  % (5398)------------------------------
% 4.11/1.04  % (5398)------------------------------
% 4.11/1.04  % (5377)Time limit reached!
% 4.11/1.04  % (5377)------------------------------
% 4.11/1.04  % (5377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/1.04  % (5377)Termination reason: Time limit
% 4.11/1.04  % (5377)Termination phase: Saturation
% 4.11/1.04  
% 4.11/1.04  % (5377)Memory used [KB]: 12025
% 4.11/1.04  % (5377)Time elapsed: 0.600 s
% 4.11/1.04  % (5377)------------------------------
% 4.11/1.04  % (5377)------------------------------
% 4.11/1.05  % (5634)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.53/1.08  % (5635)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.87/1.13  % (5641)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.87/1.13  % (5640)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.16/1.15  % (5642)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.16/1.16  % (5644)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.16/1.17  % (5643)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.16/1.23  % (5391)Time limit reached!
% 6.16/1.23  % (5391)------------------------------
% 6.16/1.23  % (5391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.16/1.23  % (5391)Termination reason: Time limit
% 6.16/1.23  % (5391)Termination phase: Saturation
% 6.16/1.23  
% 6.16/1.23  % (5391)Memory used [KB]: 6268
% 6.16/1.23  % (5391)Time elapsed: 0.800 s
% 6.16/1.23  % (5391)------------------------------
% 6.16/1.23  % (5391)------------------------------
% 7.80/1.37  % (5645)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 8.23/1.43  % (5372)Time limit reached!
% 8.23/1.43  % (5372)------------------------------
% 8.23/1.43  % (5372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.23/1.43  % (5372)Termination reason: Time limit
% 8.23/1.43  
% 8.23/1.43  % (5372)Memory used [KB]: 22643
% 8.23/1.43  % (5372)Time elapsed: 1.003 s
% 8.23/1.43  % (5372)------------------------------
% 8.23/1.43  % (5372)------------------------------
% 9.13/1.54  % (5646)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 9.13/1.57  % (5642)Time limit reached!
% 9.13/1.57  % (5642)------------------------------
% 9.13/1.57  % (5642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.13/1.57  % (5642)Termination reason: Time limit
% 9.13/1.57  % (5642)Termination phase: Saturation
% 9.13/1.57  
% 9.13/1.57  % (5642)Memory used [KB]: 2302
% 9.13/1.57  % (5642)Time elapsed: 0.500 s
% 9.13/1.57  % (5642)------------------------------
% 9.13/1.57  % (5642)------------------------------
% 9.55/1.62  % (5396)Time limit reached!
% 9.55/1.62  % (5396)------------------------------
% 9.55/1.62  % (5396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.55/1.64  % (5396)Termination reason: Time limit
% 9.55/1.64  
% 9.55/1.64  % (5396)Memory used [KB]: 20596
% 9.55/1.64  % (5396)Time elapsed: 1.210 s
% 9.55/1.64  % (5396)------------------------------
% 9.55/1.64  % (5396)------------------------------
% 10.32/1.70  % (5647)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 10.32/1.71  % (5385)Time limit reached!
% 10.32/1.71  % (5385)------------------------------
% 10.32/1.71  % (5385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.32/1.71  % (5385)Termination reason: Time limit
% 10.32/1.71  % (5385)Termination phase: Saturation
% 10.32/1.71  
% 10.32/1.71  % (5385)Memory used [KB]: 15351
% 10.32/1.71  % (5385)Time elapsed: 1.300 s
% 10.32/1.71  % (5385)------------------------------
% 10.32/1.71  % (5385)------------------------------
% 10.73/1.73  % (5647)Refutation not found, incomplete strategy% (5647)------------------------------
% 10.73/1.73  % (5647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.73/1.73  % (5647)Termination reason: Refutation not found, incomplete strategy
% 10.73/1.73  
% 10.73/1.73  % (5647)Memory used [KB]: 6268
% 10.73/1.73  % (5647)Time elapsed: 0.147 s
% 10.73/1.73  % (5647)------------------------------
% 10.73/1.73  % (5647)------------------------------
% 10.73/1.74  % (5648)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 10.95/1.75  % (5394)Time limit reached!
% 10.95/1.75  % (5394)------------------------------
% 10.95/1.75  % (5394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.95/1.75  % (5394)Termination reason: Time limit
% 10.95/1.75  
% 10.95/1.75  % (5394)Memory used [KB]: 19445
% 10.95/1.75  % (5394)Time elapsed: 1.316 s
% 10.95/1.75  % (5394)------------------------------
% 10.95/1.75  % (5394)------------------------------
% 10.95/1.82  % (5482)Time limit reached!
% 10.95/1.82  % (5482)------------------------------
% 10.95/1.82  % (5482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.95/1.82  % (5482)Termination reason: Time limit
% 10.95/1.82  
% 10.95/1.82  % (5482)Memory used [KB]: 9850
% 10.95/1.82  % (5482)Time elapsed: 1.227 s
% 10.95/1.82  % (5482)------------------------------
% 10.95/1.82  % (5482)------------------------------
% 10.95/1.82  % (5649)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 11.51/1.87  % (5650)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 11.82/1.88  % (5646)Time limit reached!
% 11.82/1.88  % (5646)------------------------------
% 11.82/1.88  % (5646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.82/1.88  % (5646)Termination reason: Time limit
% 11.82/1.88  % (5646)Termination phase: Saturation
% 11.82/1.88  
% 11.82/1.88  % (5646)Memory used [KB]: 5884
% 11.82/1.88  % (5646)Time elapsed: 0.400 s
% 11.82/1.88  % (5646)------------------------------
% 11.82/1.88  % (5646)------------------------------
% 11.82/1.89  % (5651)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 11.82/1.92  % (5397)Time limit reached!
% 11.82/1.92  % (5397)------------------------------
% 11.82/1.92  % (5397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.82/1.92  % (5397)Termination reason: Time limit
% 11.82/1.92  % (5397)Termination phase: Saturation
% 11.82/1.92  
% 11.82/1.92  % (5397)Memory used [KB]: 11385
% 11.82/1.92  % (5397)Time elapsed: 1.520 s
% 11.82/1.92  % (5397)------------------------------
% 11.82/1.92  % (5397)------------------------------
% 12.35/1.96  % (5652)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 12.49/2.00  % (5653)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 13.01/2.05  % (5654)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 13.50/2.14  % (5649)Time limit reached!
% 13.50/2.14  % (5649)------------------------------
% 13.50/2.14  % (5649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.50/2.14  % (5649)Termination reason: Time limit
% 13.50/2.14  
% 13.50/2.14  % (5649)Memory used [KB]: 3070
% 13.50/2.14  % (5649)Time elapsed: 0.414 s
% 13.50/2.14  % (5649)------------------------------
% 13.50/2.14  % (5649)------------------------------
% 13.50/2.16  % (5653)Refutation not found, incomplete strategy% (5653)------------------------------
% 13.50/2.16  % (5653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.50/2.16  % (5653)Termination reason: Refutation not found, incomplete strategy
% 13.50/2.16  
% 13.50/2.16  % (5653)Memory used [KB]: 6268
% 13.50/2.16  % (5653)Time elapsed: 0.273 s
% 13.50/2.16  % (5653)------------------------------
% 13.50/2.16  % (5653)------------------------------
% 14.98/2.27  % (5384)Time limit reached!
% 14.98/2.27  % (5384)------------------------------
% 14.98/2.27  % (5384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.98/2.27  % (5462)Time limit reached!
% 14.98/2.27  % (5462)------------------------------
% 14.98/2.27  % (5462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.98/2.27  % (5462)Termination reason: Time limit
% 14.98/2.27  % (5462)Termination phase: Saturation
% 14.98/2.27  
% 14.98/2.27  % (5462)Memory used [KB]: 17782
% 14.98/2.27  % (5462)Time elapsed: 1.700 s
% 14.98/2.27  % (5462)------------------------------
% 14.98/2.27  % (5462)------------------------------
% 14.98/2.27  % (5655)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 15.22/2.29  % (5384)Termination reason: Time limit
% 15.22/2.29  
% 15.22/2.29  % (5384)Memory used [KB]: 6396
% 15.22/2.29  % (5384)Time elapsed: 1.828 s
% 15.22/2.29  % (5384)------------------------------
% 15.22/2.29  % (5384)------------------------------
% 15.22/2.29  % (5656)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 15.22/2.31  % (5656)Refutation not found, incomplete strategy% (5656)------------------------------
% 15.22/2.31  % (5656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.22/2.31  % (5656)Termination reason: Refutation not found, incomplete strategy
% 15.22/2.31  
% 15.22/2.31  % (5656)Memory used [KB]: 6268
% 15.22/2.31  % (5656)Time elapsed: 0.100 s
% 15.22/2.31  % (5656)------------------------------
% 15.22/2.31  % (5656)------------------------------
% 15.55/2.34  % (5654)Time limit reached!
% 15.55/2.34  % (5654)------------------------------
% 15.55/2.34  % (5654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.68/2.34  % (5654)Termination reason: Time limit
% 15.68/2.34  % (5654)Termination phase: Saturation
% 15.68/2.34  
% 15.68/2.34  % (5654)Memory used [KB]: 11001
% 15.68/2.34  % (5654)Time elapsed: 0.400 s
% 15.68/2.34  % (5654)------------------------------
% 15.68/2.34  % (5654)------------------------------
% 15.68/2.38  % (5657)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 15.68/2.41  % (5395)Refutation found. Thanks to Tanya!
% 15.68/2.41  % SZS status Theorem for theBenchmark
% 15.68/2.41  % SZS output start Proof for theBenchmark
% 15.68/2.41  fof(f31877,plain,(
% 15.68/2.41    $false),
% 15.68/2.41    inference(avatar_sat_refutation,[],[f242,f243,f248,f249,f250,f411,f416,f421,f426,f505,f729,f974,f2121,f2287,f2384,f12330,f31876])).
% 16.29/2.42  fof(f31876,plain,(
% 16.29/2.42    spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_9 | ~spl16_10),
% 16.29/2.42    inference(avatar_contradiction_clause,[],[f31875])).
% 16.29/2.42  fof(f31875,plain,(
% 16.29/2.42    $false | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_9 | ~spl16_10)),
% 16.29/2.42    inference(subsumption_resolution,[],[f31844,f573])).
% 16.29/2.42  fof(f573,plain,(
% 16.29/2.42    ( ! [X0] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_10)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f425,f233,f358,f151])).
% 16.29/2.42  fof(f151,plain,(
% 16.29/2.42    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f87])).
% 16.29/2.42  fof(f87,plain,(
% 16.29/2.42    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f84,f86,f85])).
% 16.29/2.42  fof(f85,plain,(
% 16.29/2.42    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f86,plain,(
% 16.29/2.42    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f84,plain,(
% 16.29/2.42    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(rectify,[],[f83])).
% 16.29/2.42  fof(f83,plain,(
% 16.29/2.42    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(nnf_transformation,[],[f45])).
% 16.29/2.42  fof(f45,plain,(
% 16.29/2.42    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(flattening,[],[f44])).
% 16.29/2.42  fof(f44,plain,(
% 16.29/2.42    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.42    inference(ennf_transformation,[],[f11])).
% 16.29/2.42  fof(f11,axiom,(
% 16.29/2.42    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 16.29/2.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 16.29/2.42  fof(f358,plain,(
% 16.29/2.42    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl16_1 | ~spl16_4)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f236,f182])).
% 16.29/2.42  fof(f182,plain,(
% 16.29/2.42    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f67])).
% 16.29/2.42  fof(f67,plain,(
% 16.29/2.42    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(flattening,[],[f66])).
% 16.29/2.42  fof(f66,plain,(
% 16.29/2.42    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.42    inference(ennf_transformation,[],[f15])).
% 16.29/2.42  fof(f15,axiom,(
% 16.29/2.42    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 16.29/2.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 16.29/2.42  fof(f236,plain,(
% 16.29/2.42    l3_lattices(sK0) | ~spl16_4),
% 16.29/2.42    inference(avatar_component_clause,[],[f235])).
% 16.29/2.42  fof(f235,plain,(
% 16.29/2.42    spl16_4 <=> l3_lattices(sK0)),
% 16.29/2.42    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 16.29/2.42  fof(f233,plain,(
% 16.29/2.42    ~v13_lattices(sK0) | spl16_3),
% 16.29/2.42    inference(avatar_component_clause,[],[f231])).
% 16.29/2.42  fof(f231,plain,(
% 16.29/2.42    spl16_3 <=> v13_lattices(sK0)),
% 16.29/2.42    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).
% 16.29/2.42  fof(f425,plain,(
% 16.29/2.42    l1_lattices(sK0) | ~spl16_10),
% 16.29/2.42    inference(avatar_component_clause,[],[f423])).
% 16.29/2.42  fof(f423,plain,(
% 16.29/2.42    spl16_10 <=> l1_lattices(sK0)),
% 16.29/2.42    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).
% 16.29/2.42  fof(f224,plain,(
% 16.29/2.42    ~v2_struct_0(sK0) | spl16_1),
% 16.29/2.42    inference(avatar_component_clause,[],[f223])).
% 16.29/2.42  fof(f223,plain,(
% 16.29/2.42    spl16_1 <=> v2_struct_0(sK0)),
% 16.29/2.42    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 16.29/2.42  fof(f31844,plain,(
% 16.29/2.42    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_9 | ~spl16_10)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f415,f410,f236,f358,f12606,f14477,f141])).
% 16.29/2.42  fof(f141,plain,(
% 16.29/2.42    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f78])).
% 16.29/2.42  fof(f78,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(nnf_transformation,[],[f39])).
% 16.29/2.42  fof(f39,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(flattening,[],[f38])).
% 16.29/2.42  fof(f38,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.42    inference(ennf_transformation,[],[f10])).
% 16.29/2.42  fof(f10,axiom,(
% 16.29/2.42    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 16.29/2.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 16.29/2.42  fof(f14477,plain,(
% 16.29/2.42    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_9 | ~spl16_10)),
% 16.29/2.42    inference(duplicate_literal_removal,[],[f14473])).
% 16.29/2.42  fof(f14473,plain,(
% 16.29/2.42    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_9 | ~spl16_10)),
% 16.29/2.42    inference(superposition,[],[f624,f1509])).
% 16.29/2.42  fof(f1509,plain,(
% 16.29/2.42    ( ! [X0,X1] : (k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_9 | ~spl16_10)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f425,f420,f358,f573,f153])).
% 16.29/2.42  fof(f153,plain,(
% 16.29/2.42    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f92])).
% 16.29/2.42  fof(f92,plain,(
% 16.29/2.42    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f89,f91,f90])).
% 16.29/2.42  fof(f90,plain,(
% 16.29/2.42    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f91,plain,(
% 16.29/2.42    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f89,plain,(
% 16.29/2.42    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(rectify,[],[f88])).
% 16.29/2.42  fof(f88,plain,(
% 16.29/2.42    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(nnf_transformation,[],[f47])).
% 16.29/2.42  fof(f47,plain,(
% 16.29/2.42    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(flattening,[],[f46])).
% 16.29/2.42  fof(f46,plain,(
% 16.29/2.42    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.42    inference(ennf_transformation,[],[f14])).
% 16.29/2.42  fof(f14,axiom,(
% 16.29/2.42    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 16.29/2.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 16.29/2.42  fof(f420,plain,(
% 16.29/2.42    v6_lattices(sK0) | ~spl16_9),
% 16.29/2.42    inference(avatar_component_clause,[],[f418])).
% 16.29/2.42  fof(f418,plain,(
% 16.29/2.42    spl16_9 <=> v6_lattices(sK0)),
% 16.29/2.42    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).
% 16.29/2.42  fof(f624,plain,(
% 16.29/2.42    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_10)),
% 16.29/2.42    inference(subsumption_resolution,[],[f623,f224])).
% 16.29/2.42  fof(f623,plain,(
% 16.29/2.42    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | v2_struct_0(sK0)) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_10)),
% 16.29/2.42    inference(subsumption_resolution,[],[f622,f425])).
% 16.29/2.42  fof(f622,plain,(
% 16.29/2.42    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | spl16_3 | ~spl16_4)),
% 16.29/2.42    inference(subsumption_resolution,[],[f591,f233])).
% 16.29/2.42  fof(f591,plain,(
% 16.29/2.42    ( ! [X16] : (v13_lattices(sK0) | k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4)),
% 16.29/2.42    inference(resolution,[],[f358,f152])).
% 16.29/2.42  fof(f152,plain,(
% 16.29/2.42    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f87])).
% 16.29/2.42  fof(f12606,plain,(
% 16.29/2.42    ( ! [X4] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X4)))) ) | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_10)),
% 16.29/2.42    inference(superposition,[],[f4324,f1520])).
% 16.29/2.42  fof(f1520,plain,(
% 16.29/2.42    ( ! [X0] : (sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0))))) ) | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_10)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f573,f160])).
% 16.29/2.42  fof(f160,plain,(
% 16.29/2.42    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f53])).
% 16.29/2.42  fof(f53,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(flattening,[],[f52])).
% 16.29/2.42  fof(f52,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.42    inference(ennf_transformation,[],[f22])).
% 16.29/2.42  fof(f22,axiom,(
% 16.29/2.42    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 16.29/2.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 16.29/2.42  fof(f247,plain,(
% 16.29/2.42    v4_lattice3(sK0) | ~spl16_6),
% 16.29/2.42    inference(avatar_component_clause,[],[f245])).
% 16.29/2.42  fof(f245,plain,(
% 16.29/2.42    spl16_6 <=> v4_lattice3(sK0)),
% 16.29/2.42    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).
% 16.29/2.42  fof(f228,plain,(
% 16.29/2.42    v10_lattices(sK0) | ~spl16_2),
% 16.29/2.42    inference(avatar_component_clause,[],[f227])).
% 16.29/2.42  fof(f227,plain,(
% 16.29/2.42    spl16_2 <=> v10_lattices(sK0)),
% 16.29/2.42    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 16.29/2.42  fof(f4324,plain,(
% 16.29/2.42    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f236,f358,f358,f1642,f1249,f177])).
% 16.29/2.42  fof(f177,plain,(
% 16.29/2.42    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f108])).
% 16.29/2.42  fof(f108,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f106,f107])).
% 16.29/2.42  fof(f107,plain,(
% 16.29/2.42    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f106,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(rectify,[],[f105])).
% 16.29/2.42  fof(f105,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(nnf_transformation,[],[f63])).
% 16.29/2.42  fof(f63,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.42    inference(flattening,[],[f62])).
% 16.29/2.42  fof(f62,plain,(
% 16.29/2.42    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.42    inference(ennf_transformation,[],[f12])).
% 16.29/2.42  fof(f12,axiom,(
% 16.29/2.42    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 16.29/2.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 16.29/2.42  fof(f1249,plain,(
% 16.29/2.42    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f358,f430,f358,f787,f215])).
% 16.29/2.42  fof(f215,plain,(
% 16.29/2.42    ( ! [X4,X2,X3,X1] : (r2_hidden(X3,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 16.29/2.42    inference(equality_resolution,[],[f199])).
% 16.29/2.42  fof(f199,plain,(
% 16.29/2.42    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f123])).
% 16.29/2.42  fof(f123,plain,(
% 16.29/2.42    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK13(X0,X1,X2),X2) & r3_lattices(X1,sK13(X0,X1,X2),sK12(X0,X1,X2)) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))) & sK12(X0,X1,X2) = X0 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f120,f122,f121])).
% 16.29/2.42  fof(f121,plain,(
% 16.29/2.42    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK12(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) & sK12(X0,X1,X2) = X0 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f122,plain,(
% 16.29/2.42    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK12(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK13(X0,X1,X2),X2) & r3_lattices(X1,sK13(X0,X1,X2),sK12(X0,X1,X2)) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f120,plain,(
% 16.29/2.42    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.42    inference(rectify,[],[f119])).
% 16.29/2.42  fof(f119,plain,(
% 16.29/2.42    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.42    inference(nnf_transformation,[],[f73])).
% 16.29/2.42  fof(f73,plain,(
% 16.29/2.42    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.42    inference(flattening,[],[f72])).
% 16.29/2.42  fof(f72,plain,(
% 16.29/2.42    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 16.29/2.42    inference(ennf_transformation,[],[f19])).
% 16.29/2.42  fof(f19,axiom,(
% 16.29/2.42    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 16.29/2.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).
% 16.29/2.42  fof(f787,plain,(
% 16.29/2.42    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.42    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f358,f572,f214])).
% 16.29/2.42  fof(f214,plain,(
% 16.29/2.42    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 16.29/2.42    inference(equality_resolution,[],[f193])).
% 16.29/2.42  fof(f193,plain,(
% 16.29/2.42    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 16.29/2.42    inference(cnf_transformation,[],[f118])).
% 16.29/2.42  fof(f118,plain,(
% 16.29/2.42    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK11(X0,X1,X2),X2) & sK11(X0,X1,X2) = X0 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f116,f117])).
% 16.29/2.42  fof(f117,plain,(
% 16.29/2.42    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK11(X0,X1,X2),X2) & sK11(X0,X1,X2) = X0 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 16.29/2.42    introduced(choice_axiom,[])).
% 16.29/2.42  fof(f116,plain,(
% 16.29/2.42    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.42    inference(rectify,[],[f115])).
% 16.29/2.43  fof(f115,plain,(
% 16.29/2.43    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.43    inference(nnf_transformation,[],[f71])).
% 16.29/2.43  fof(f71,plain,(
% 16.29/2.43    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 16.29/2.43    inference(flattening,[],[f70])).
% 16.29/2.43  fof(f70,plain,(
% 16.29/2.43    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 16.29/2.43    inference(ennf_transformation,[],[f17])).
% 16.29/2.43  fof(f17,axiom,(
% 16.29/2.43    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 16.29/2.43  fof(f572,plain,(
% 16.29/2.43    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f358,f221])).
% 16.29/2.43  fof(f221,plain,(
% 16.29/2.43    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(duplicate_literal_removal,[],[f211])).
% 16.29/2.43  fof(f211,plain,(
% 16.29/2.43    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(equality_resolution,[],[f172])).
% 16.29/2.43  fof(f172,plain,(
% 16.29/2.43    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(cnf_transformation,[],[f104])).
% 16.29/2.43  fof(f104,plain,(
% 16.29/2.43    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f102,f103])).
% 16.29/2.43  fof(f103,plain,(
% 16.29/2.43    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 16.29/2.43    introduced(choice_axiom,[])).
% 16.29/2.43  fof(f102,plain,(
% 16.29/2.43    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(rectify,[],[f101])).
% 16.29/2.43  fof(f101,plain,(
% 16.29/2.43    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f100])).
% 16.29/2.43  fof(f100,plain,(
% 16.29/2.43    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(nnf_transformation,[],[f61])).
% 16.29/2.43  fof(f61,plain,(
% 16.29/2.43    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f60])).
% 16.29/2.43  fof(f60,plain,(
% 16.29/2.43    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.43    inference(ennf_transformation,[],[f13])).
% 16.29/2.43  fof(f13,axiom,(
% 16.29/2.43    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 16.29/2.43  fof(f430,plain,(
% 16.29/2.43    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(unit_resulting_resolution,[],[f134,f224,f228,f236,f247,f167])).
% 16.29/2.43  fof(f167,plain,(
% 16.29/2.43    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~r1_tarski(X1,X2) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(cnf_transformation,[],[f57])).
% 16.29/2.43  fof(f57,plain,(
% 16.29/2.43    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f56])).
% 16.29/2.43  fof(f56,plain,(
% 16.29/2.43    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.43    inference(ennf_transformation,[],[f23])).
% 16.29/2.43  fof(f23,axiom,(
% 16.29/2.43    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_lattice3)).
% 16.29/2.43  fof(f134,plain,(
% 16.29/2.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 16.29/2.43    inference(cnf_transformation,[],[f3])).
% 16.29/2.43  fof(f3,axiom,(
% 16.29/2.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 16.29/2.43  fof(f1642,plain,(
% 16.29/2.43    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0)))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(superposition,[],[f1433,f427])).
% 16.29/2.43  fof(f427,plain,(
% 16.29/2.43    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(unit_resulting_resolution,[],[f224,f228,f236,f247,f157])).
% 16.29/2.43  fof(f157,plain,(
% 16.29/2.43    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(cnf_transformation,[],[f49])).
% 16.29/2.43  fof(f49,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f48])).
% 16.29/2.43  fof(f48,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.43    inference(ennf_transformation,[],[f21])).
% 16.29/2.43  fof(f21,axiom,(
% 16.29/2.43    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 16.29/2.43  fof(f1433,plain,(
% 16.29/2.43    ( ! [X21] : (r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(subsumption_resolution,[],[f1432,f224])).
% 16.29/2.43  fof(f1432,plain,(
% 16.29/2.43    ( ! [X21] : (r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21)) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(subsumption_resolution,[],[f1431,f228])).
% 16.29/2.43  fof(f1431,plain,(
% 16.29/2.43    ( ! [X21] : (r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(subsumption_resolution,[],[f1430,f247])).
% 16.29/2.43  fof(f1430,plain,(
% 16.29/2.43    ( ! [X21] : (r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(subsumption_resolution,[],[f1429,f236])).
% 16.29/2.43  fof(f1429,plain,(
% 16.29/2.43    ( ! [X21] : (r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(subsumption_resolution,[],[f1410,f357])).
% 16.29/2.43  fof(f357,plain,(
% 16.29/2.43    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl16_1 | ~spl16_4)),
% 16.29/2.43    inference(unit_resulting_resolution,[],[f224,f236,f181])).
% 16.29/2.43  fof(f181,plain,(
% 16.29/2.43    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(cnf_transformation,[],[f65])).
% 16.29/2.43  fof(f65,plain,(
% 16.29/2.43    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f64])).
% 16.29/2.43  fof(f64,plain,(
% 16.29/2.43    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.43    inference(ennf_transformation,[],[f16])).
% 16.29/2.43  fof(f16,axiom,(
% 16.29/2.43    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 16.29/2.43  fof(f1410,plain,(
% 16.29/2.43    ( ! [X21] : (r3_lattice3(sK0,k16_lattice3(sK0,X21),a_2_6_lattice3(sK0,X21)) | ~m1_subset_1(k16_lattice3(sK0,X21),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(superposition,[],[f209,f429])).
% 16.29/2.43  fof(f429,plain,(
% 16.29/2.43    ( ! [X0] : (k16_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.43    inference(unit_resulting_resolution,[],[f224,f228,f236,f247,f159])).
% 16.29/2.43  fof(f159,plain,(
% 16.29/2.43    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(cnf_transformation,[],[f51])).
% 16.29/2.43  fof(f51,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f50])).
% 16.29/2.43  fof(f50,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.43    inference(ennf_transformation,[],[f24])).
% 16.29/2.43  fof(f24,axiom,(
% 16.29/2.43    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).
% 16.29/2.43  fof(f209,plain,(
% 16.29/2.43    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(equality_resolution,[],[f162])).
% 16.29/2.43  fof(f162,plain,(
% 16.29/2.43    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.43    inference(cnf_transformation,[],[f97])).
% 16.29/2.43  fof(f97,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f95,f96])).
% 16.29/2.43  fof(f96,plain,(
% 16.29/2.43    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 16.29/2.43    introduced(choice_axiom,[])).
% 16.29/2.43  fof(f95,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(rectify,[],[f94])).
% 16.29/2.43  fof(f94,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f93])).
% 16.29/2.43  fof(f93,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(nnf_transformation,[],[f55])).
% 16.29/2.43  fof(f55,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.43    inference(flattening,[],[f54])).
% 16.29/2.43  fof(f54,plain,(
% 16.29/2.43    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.43    inference(ennf_transformation,[],[f20])).
% 16.29/2.43  fof(f20,axiom,(
% 16.29/2.43    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 16.29/2.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 16.29/2.43  fof(f410,plain,(
% 16.29/2.43    v9_lattices(sK0) | ~spl16_7),
% 16.29/2.43    inference(avatar_component_clause,[],[f408])).
% 16.29/2.43  fof(f408,plain,(
% 16.29/2.43    spl16_7 <=> v9_lattices(sK0)),
% 16.29/2.43    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).
% 16.29/2.43  fof(f415,plain,(
% 16.29/2.43    v8_lattices(sK0) | ~spl16_8),
% 16.29/2.43    inference(avatar_component_clause,[],[f413])).
% 16.29/2.43  fof(f413,plain,(
% 16.29/2.43    spl16_8 <=> v8_lattices(sK0)),
% 16.29/2.43    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).
% 16.29/2.43  fof(f12330,plain,(
% 16.29/2.43    spl16_1 | ~spl16_4 | spl16_5 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_29 | ~spl16_52),
% 16.29/2.43    inference(avatar_contradiction_clause,[],[f12329])).
% 16.29/2.43  fof(f12329,plain,(
% 16.29/2.43    $false | (spl16_1 | ~spl16_4 | spl16_5 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_29 | ~spl16_52)),
% 16.29/2.43    inference(subsumption_resolution,[],[f12328,f241])).
% 16.29/2.43  fof(f241,plain,(
% 16.29/2.43    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl16_5),
% 16.29/2.43    inference(avatar_component_clause,[],[f239])).
% 16.29/2.43  fof(f239,plain,(
% 16.29/2.43    spl16_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 16.29/2.43    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).
% 16.29/2.43  fof(f12328,plain,(
% 16.29/2.43    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl16_1 | ~spl16_4 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_29 | ~spl16_52)),
% 16.29/2.43    inference(forward_demodulation,[],[f12327,f973])).
% 16.29/2.43  fof(f973,plain,(
% 16.29/2.43    ( ! [X42] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0))) ) | ~spl16_29),
% 16.29/2.43    inference(avatar_component_clause,[],[f972])).
% 16.29/2.43  fof(f972,plain,(
% 16.29/2.43    spl16_29 <=> ! [X42] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0))),
% 16.29/2.43    introduced(avatar_definition,[new_symbols(naming,[spl16_29])])).
% 16.29/2.43  fof(f12327,plain,(
% 16.29/2.43    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl16_1 | ~spl16_4 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_52)),
% 16.29/2.43    inference(subsumption_resolution,[],[f12326,f224])).
% 16.29/2.43  fof(f12326,plain,(
% 16.29/2.43    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_52)),
% 16.29/2.43    inference(subsumption_resolution,[],[f12325,f415])).
% 16.29/2.43  fof(f12325,plain,(
% 16.29/2.43    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_7 | ~spl16_11 | ~spl16_52)),
% 16.29/2.43    inference(subsumption_resolution,[],[f12324,f410])).
% 16.29/2.43  fof(f12324,plain,(
% 16.29/2.43    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_11 | ~spl16_52)),
% 16.29/2.43    inference(subsumption_resolution,[],[f12323,f236])).
% 16.29/2.43  fof(f12323,plain,(
% 16.29/2.43    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_11 | ~spl16_52)),
% 16.29/2.43    inference(subsumption_resolution,[],[f12322,f358])).
% 16.29/2.43  fof(f12322,plain,(
% 16.29/2.43    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl16_11 | ~spl16_52)),
% 16.29/2.43    inference(subsumption_resolution,[],[f12312,f504])).
% 16.29/2.44  fof(f504,plain,(
% 16.29/2.44    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl16_11),
% 16.29/2.44    inference(avatar_component_clause,[],[f502])).
% 16.29/2.44  fof(f502,plain,(
% 16.29/2.44    spl16_11 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 16.29/2.44    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).
% 16.29/2.44  fof(f12312,plain,(
% 16.29/2.44    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | ~spl16_52),
% 16.29/2.44    inference(resolution,[],[f2381,f141])).
% 16.29/2.44  fof(f2381,plain,(
% 16.29/2.44    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl16_52),
% 16.29/2.44    inference(avatar_component_clause,[],[f2379])).
% 16.29/2.44  fof(f2379,plain,(
% 16.29/2.44    spl16_52 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 16.29/2.44    introduced(avatar_definition,[new_symbols(naming,[spl16_52])])).
% 16.29/2.44  fof(f2384,plain,(
% 16.29/2.44    spl16_52 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_51),
% 16.29/2.44    inference(avatar_split_clause,[],[f2383,f2284,f502,f245,f235,f227,f223,f2379])).
% 16.29/2.44  fof(f2284,plain,(
% 16.29/2.44    spl16_51 <=> r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))),
% 16.29/2.44    introduced(avatar_definition,[new_symbols(naming,[spl16_51])])).
% 16.29/2.44  fof(f2383,plain,(
% 16.29/2.44    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_51)),
% 16.29/2.44    inference(forward_demodulation,[],[f2360,f427])).
% 16.29/2.44  fof(f2360,plain,(
% 16.29/2.44    r1_lattices(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)),k5_lattices(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_51)),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f224,f236,f504,f357,f1433,f2286,f177])).
% 16.29/2.44  fof(f2286,plain,(
% 16.29/2.44    r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) | ~spl16_51),
% 16.29/2.44    inference(avatar_component_clause,[],[f2284])).
% 16.29/2.44  fof(f2287,plain,(
% 16.29/2.44    spl16_51 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_49),
% 16.29/2.44    inference(avatar_split_clause,[],[f2274,f2118,f502,f245,f235,f227,f223,f2284])).
% 16.29/2.44  fof(f2118,plain,(
% 16.29/2.44    spl16_49 <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 16.29/2.44    introduced(avatar_definition,[new_symbols(naming,[spl16_49])])).
% 16.29/2.44  fof(f2274,plain,(
% 16.29/2.44    r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_49)),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f787,f504,f358,f2120,f215])).
% 16.29/2.44  fof(f2120,plain,(
% 16.29/2.44    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl16_49),
% 16.29/2.44    inference(avatar_component_clause,[],[f2118])).
% 16.29/2.44  fof(f2121,plain,(
% 16.29/2.44    spl16_49 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_12),
% 16.29/2.44    inference(avatar_split_clause,[],[f2084,f688,f245,f235,f227,f223,f2118])).
% 16.29/2.44  fof(f688,plain,(
% 16.29/2.44    spl16_12 <=> k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 16.29/2.44    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).
% 16.29/2.44  fof(f2084,plain,(
% 16.29/2.44    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_12)),
% 16.29/2.44    inference(superposition,[],[f1666,f690])).
% 16.29/2.44  fof(f690,plain,(
% 16.29/2.44    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~spl16_12),
% 16.29/2.44    inference(avatar_component_clause,[],[f688])).
% 16.29/2.44  fof(f1666,plain,(
% 16.29/2.44    ( ! [X1] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k16_lattice3(sK0,X1))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.44    inference(superposition,[],[f430,f510])).
% 16.29/2.44  fof(f510,plain,(
% 16.29/2.44    ( ! [X0] : (k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k16_lattice3(sK0,X0)))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f224,f228,f247,f236,f357,f160])).
% 16.29/2.44  fof(f974,plain,(
% 16.29/2.44    ~spl16_3 | spl16_29 | spl16_1 | ~spl16_4 | ~spl16_10 | ~spl16_11),
% 16.29/2.44    inference(avatar_split_clause,[],[f970,f502,f423,f235,f223,f972,f231])).
% 16.29/2.44  fof(f970,plain,(
% 16.29/2.44    ( ! [X42] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0)) | ~v13_lattices(sK0)) ) | (spl16_1 | ~spl16_4 | ~spl16_10 | ~spl16_11)),
% 16.29/2.44    inference(subsumption_resolution,[],[f969,f224])).
% 16.29/2.44  fof(f969,plain,(
% 16.29/2.44    ( ! [X42] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0)) | ~v13_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4 | ~spl16_10 | ~spl16_11)),
% 16.29/2.44    inference(subsumption_resolution,[],[f968,f425])).
% 16.29/2.44  fof(f968,plain,(
% 16.29/2.44    ( ! [X42] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4 | ~spl16_11)),
% 16.29/2.44    inference(subsumption_resolution,[],[f605,f504])).
% 16.29/2.44  fof(f605,plain,(
% 16.29/2.44    ( ! [X42] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X42),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4)),
% 16.29/2.44    inference(resolution,[],[f358,f206])).
% 16.29/2.44  fof(f206,plain,(
% 16.29/2.44    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.44    inference(equality_resolution,[],[f145])).
% 16.29/2.44  fof(f145,plain,(
% 16.29/2.44    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.44    inference(cnf_transformation,[],[f82])).
% 16.29/2.44  fof(f82,plain,(
% 16.29/2.44    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f80,f81])).
% 16.29/2.44  fof(f81,plain,(
% 16.29/2.44    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 16.29/2.44    introduced(choice_axiom,[])).
% 16.29/2.44  fof(f80,plain,(
% 16.29/2.44    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.44    inference(rectify,[],[f79])).
% 16.29/2.44  fof(f79,plain,(
% 16.29/2.44    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.44    inference(nnf_transformation,[],[f43])).
% 16.29/2.44  fof(f43,plain,(
% 16.29/2.44    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.44    inference(flattening,[],[f42])).
% 16.29/2.44  fof(f42,plain,(
% 16.29/2.44    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.44    inference(ennf_transformation,[],[f7])).
% 16.29/2.44  fof(f7,axiom,(
% 16.29/2.44    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 16.29/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 16.29/2.44  fof(f729,plain,(
% 16.29/2.44    spl16_12 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11),
% 16.29/2.44    inference(avatar_split_clause,[],[f728,f502,f245,f235,f227,f223,f688])).
% 16.29/2.44  fof(f728,plain,(
% 16.29/2.44    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11)),
% 16.29/2.44    inference(subsumption_resolution,[],[f727,f224])).
% 16.29/2.44  fof(f727,plain,(
% 16.29/2.44    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11)),
% 16.29/2.44    inference(subsumption_resolution,[],[f726,f228])).
% 16.29/2.44  fof(f726,plain,(
% 16.29/2.44    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl16_4 | ~spl16_6 | ~spl16_11)),
% 16.29/2.44    inference(subsumption_resolution,[],[f725,f247])).
% 16.29/2.44  fof(f725,plain,(
% 16.29/2.44    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl16_4 | ~spl16_11)),
% 16.29/2.44    inference(subsumption_resolution,[],[f663,f236])).
% 16.29/2.44  fof(f663,plain,(
% 16.29/2.44    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl16_11),
% 16.29/2.44    inference(resolution,[],[f504,f161])).
% 16.29/2.44  fof(f161,plain,(
% 16.29/2.44    ( ! [X0,X1] : (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.44    inference(cnf_transformation,[],[f53])).
% 16.29/2.44  fof(f505,plain,(
% 16.29/2.44    spl16_11 | spl16_1 | ~spl16_10),
% 16.29/2.44    inference(avatar_split_clause,[],[f486,f423,f223,f502])).
% 16.29/2.44  fof(f486,plain,(
% 16.29/2.44    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl16_1 | ~spl16_10)),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f224,f425,f143])).
% 16.29/2.44  fof(f143,plain,(
% 16.29/2.44    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 16.29/2.44    inference(cnf_transformation,[],[f41])).
% 16.29/2.44  fof(f41,plain,(
% 16.29/2.44    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 16.29/2.44    inference(flattening,[],[f40])).
% 16.29/2.44  fof(f40,plain,(
% 16.29/2.44    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 16.29/2.44    inference(ennf_transformation,[],[f8])).
% 16.29/2.44  fof(f8,axiom,(
% 16.29/2.44    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 16.29/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 16.29/2.44  fof(f426,plain,(
% 16.29/2.44    spl16_10 | ~spl16_4),
% 16.29/2.44    inference(avatar_split_clause,[],[f353,f235,f423])).
% 16.29/2.44  fof(f353,plain,(
% 16.29/2.44    l1_lattices(sK0) | ~spl16_4),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f236,f135])).
% 16.29/2.44  fof(f135,plain,(
% 16.29/2.44    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 16.29/2.44    inference(cnf_transformation,[],[f34])).
% 16.29/2.44  fof(f34,plain,(
% 16.29/2.44    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 16.29/2.44    inference(ennf_transformation,[],[f28])).
% 16.29/2.44  fof(f28,plain,(
% 16.29/2.44    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 16.29/2.44    inference(pure_predicate_removal,[],[f9])).
% 16.29/2.44  fof(f9,axiom,(
% 16.29/2.44    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 16.29/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 16.29/2.44  fof(f421,plain,(
% 16.29/2.44    spl16_9 | spl16_1 | ~spl16_2 | ~spl16_4),
% 16.29/2.44    inference(avatar_split_clause,[],[f354,f235,f227,f223,f418])).
% 16.29/2.44  fof(f354,plain,(
% 16.29/2.44    v6_lattices(sK0) | (spl16_1 | ~spl16_2 | ~spl16_4)),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f224,f228,f236,f137])).
% 16.29/2.44  fof(f137,plain,(
% 16.29/2.44    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 16.29/2.44    inference(cnf_transformation,[],[f36])).
% 16.29/2.44  fof(f36,plain,(
% 16.29/2.44    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 16.29/2.44    inference(flattening,[],[f35])).
% 16.29/2.44  fof(f35,plain,(
% 16.29/2.44    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 16.29/2.44    inference(ennf_transformation,[],[f31])).
% 16.29/2.44  fof(f31,plain,(
% 16.29/2.44    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 16.29/2.44    inference(pure_predicate_removal,[],[f30])).
% 16.29/2.44  fof(f30,plain,(
% 16.29/2.44    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 16.29/2.44    inference(pure_predicate_removal,[],[f29])).
% 16.29/2.44  fof(f29,plain,(
% 16.29/2.44    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 16.29/2.44    inference(pure_predicate_removal,[],[f6])).
% 16.29/2.44  fof(f6,axiom,(
% 16.29/2.44    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 16.29/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 16.29/2.44  fof(f416,plain,(
% 16.29/2.44    spl16_8 | spl16_1 | ~spl16_2 | ~spl16_4),
% 16.29/2.44    inference(avatar_split_clause,[],[f355,f235,f227,f223,f413])).
% 16.29/2.44  fof(f355,plain,(
% 16.29/2.44    v8_lattices(sK0) | (spl16_1 | ~spl16_2 | ~spl16_4)),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f224,f228,f236,f138])).
% 16.29/2.44  fof(f138,plain,(
% 16.29/2.44    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 16.29/2.44    inference(cnf_transformation,[],[f36])).
% 16.29/2.44  fof(f411,plain,(
% 16.29/2.44    spl16_7 | spl16_1 | ~spl16_2 | ~spl16_4),
% 16.29/2.44    inference(avatar_split_clause,[],[f356,f235,f227,f223,f408])).
% 16.29/2.44  fof(f356,plain,(
% 16.29/2.44    v9_lattices(sK0) | (spl16_1 | ~spl16_2 | ~spl16_4)),
% 16.29/2.44    inference(unit_resulting_resolution,[],[f224,f228,f236,f139])).
% 16.29/2.44  fof(f139,plain,(
% 16.29/2.44    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 16.29/2.44    inference(cnf_transformation,[],[f36])).
% 16.29/2.44  fof(f250,plain,(
% 16.29/2.44    ~spl16_1),
% 16.29/2.44    inference(avatar_split_clause,[],[f129,f223])).
% 16.29/2.44  fof(f129,plain,(
% 16.29/2.44    ~v2_struct_0(sK0)),
% 16.29/2.44    inference(cnf_transformation,[],[f77])).
% 16.29/2.44  fof(f77,plain,(
% 16.29/2.44    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 16.29/2.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f76])).
% 16.29/2.44  fof(f76,plain,(
% 16.29/2.44    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 16.29/2.44    introduced(choice_axiom,[])).
% 16.29/2.44  fof(f33,plain,(
% 16.29/2.44    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 16.29/2.44    inference(flattening,[],[f32])).
% 16.29/2.44  fof(f32,plain,(
% 16.29/2.44    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 16.29/2.44    inference(ennf_transformation,[],[f27])).
% 16.29/2.44  fof(f27,negated_conjecture,(
% 16.29/2.44    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 16.29/2.44    inference(negated_conjecture,[],[f26])).
% 16.29/2.44  fof(f26,conjecture,(
% 16.29/2.44    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 16.29/2.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 16.29/2.44  fof(f249,plain,(
% 16.29/2.44    spl16_2),
% 16.29/2.44    inference(avatar_split_clause,[],[f130,f227])).
% 16.29/2.44  fof(f130,plain,(
% 16.29/2.44    v10_lattices(sK0)),
% 16.29/2.44    inference(cnf_transformation,[],[f77])).
% 16.29/2.44  fof(f248,plain,(
% 16.29/2.44    spl16_6),
% 16.29/2.44    inference(avatar_split_clause,[],[f131,f245])).
% 16.29/2.44  fof(f131,plain,(
% 16.29/2.44    v4_lattice3(sK0)),
% 16.29/2.44    inference(cnf_transformation,[],[f77])).
% 16.29/2.44  fof(f243,plain,(
% 16.29/2.44    spl16_4),
% 16.29/2.44    inference(avatar_split_clause,[],[f132,f235])).
% 16.29/2.44  fof(f132,plain,(
% 16.29/2.44    l3_lattices(sK0)),
% 16.29/2.44    inference(cnf_transformation,[],[f77])).
% 16.29/2.44  fof(f242,plain,(
% 16.29/2.44    spl16_1 | ~spl16_2 | ~spl16_3 | ~spl16_4 | ~spl16_5),
% 16.29/2.44    inference(avatar_split_clause,[],[f133,f239,f235,f231,f227,f223])).
% 16.29/2.44  fof(f133,plain,(
% 16.29/2.44    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 16.29/2.44    inference(cnf_transformation,[],[f77])).
% 16.29/2.44  % SZS output end Proof for theBenchmark
% 16.29/2.44  % (5395)------------------------------
% 16.29/2.44  % (5395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.44  % (5395)Termination reason: Refutation
% 16.29/2.44  
% 16.29/2.44  % (5395)Memory used [KB]: 24946
% 16.29/2.44  % (5395)Time elapsed: 2.012 s
% 16.29/2.44  % (5395)------------------------------
% 16.29/2.44  % (5395)------------------------------
% 16.29/2.44  % (5376)Time limit reached!
% 16.29/2.44  % (5376)------------------------------
% 16.29/2.44  % (5376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.29/2.44  % (5376)Termination reason: Time limit
% 16.29/2.44  % (5376)Termination phase: Saturation
% 16.29/2.44  
% 16.29/2.44  % (5376)Memory used [KB]: 25458
% 16.29/2.44  % (5376)Time elapsed: 2.0000 s
% 16.29/2.44  % (5376)------------------------------
% 16.29/2.44  % (5376)------------------------------
% 16.29/2.44  % (5369)Success in time 2.084 s
%------------------------------------------------------------------------------
