%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:47 EST 2020

% Result     : Theorem 11.12s
% Output     : Refutation 11.29s
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
fof(f22719,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f247,f248,f253,f254,f255,f413,f418,f423,f428,f500,f723,f1066,f5001,f5298,f5459,f9429,f22718])).

fof(f22718,plain,
    ( spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(avatar_contradiction_clause,[],[f22717])).

fof(f22717,plain,
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
    inference(subsumption_resolution,[],[f22686,f570])).

fof(f570,plain,
    ( ! [X0] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f229,f427,f238,f361,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f88,f90,f89])).

fof(f89,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
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

fof(f88,plain,(
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
    inference(rectify,[],[f87])).

fof(f87,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f361,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f229,f241,f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f241,plain,
    ( l3_lattices(sK0)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl16_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f238,plain,
    ( ~ v13_lattices(sK0)
    | spl16_3 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl16_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f427,plain,
    ( l1_lattices(sK0)
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl16_10
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f229,plain,
    ( ~ v2_struct_0(sK0)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl16_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f22686,plain,
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
    inference(unit_resulting_resolution,[],[f229,f417,f412,f241,f361,f10243,f11698,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f11698,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(duplicate_literal_removal,[],[f11694])).

fof(f11694,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) )
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(superposition,[],[f622,f1400])).

fof(f1400,plain,
    ( ! [X0,X1] : k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f229,f427,f422,f361,f570,f156])).

fof(f156,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f93,f95,f94])).

fof(f94,plain,(
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

fof(f95,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
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
    inference(rectify,[],[f92])).

fof(f92,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f422,plain,
    ( v6_lattices(sK0)
    | ~ spl16_9 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl16_9
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f622,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) )
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f621,f229])).

fof(f621,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | v2_struct_0(sK0) )
    | spl16_1
    | spl16_3
    | ~ spl16_4
    | ~ spl16_10 ),
    inference(subsumption_resolution,[],[f620,f427])).

fof(f620,plain,
    ( ! [X16] :
        ( k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | spl16_3
    | ~ spl16_4 ),
    inference(subsumption_resolution,[],[f588,f238])).

fof(f588,plain,
    ( ! [X16] :
        ( v13_lattices(sK0)
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16))
        | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4 ),
    inference(resolution,[],[f361,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f10243,plain,
    ( ! [X4] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X4)))
    | spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_10 ),
    inference(superposition,[],[f10173,f1411])).

fof(f1411,plain,
    ( ! [X0] : sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,k15_lattice3(sK0,X0))))
    | spl16_1
    | ~ spl16_2
    | spl16_3
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f570,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

fof(f252,plain,
    ( v4_lattice3(sK0)
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl16_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f233,plain,
    ( v10_lattices(sK0)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl16_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f10173,plain,
    ( ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f241,f361,f361,f1523,f4967,f179])).

fof(f179,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X1,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f110,f111])).

fof(f111,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
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
    inference(rectify,[],[f109])).

fof(f109,plain,(
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
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(flattening,[],[f63])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f4967,plain,
    ( ! [X0] : r2_hidden(k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f863,f361,f361,f4957,f220])).

fof(f220,plain,(
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
    inference(equality_resolution,[],[f203])).

fof(f203,plain,(
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
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f124,f126,f125])).

fof(f125,plain,(
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

fof(f126,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r3_lattices(X1,X6,sK12(X0,X1,X2))
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK13(X0,X1,X2),X2)
        & r3_lattices(X1,sK13(X0,X1,X2),sK12(X0,X1,X2))
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f124,plain,(
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
    inference(rectify,[],[f123])).

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
    inference(nnf_transformation,[],[f75])).

fof(f75,plain,(
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
    inference(flattening,[],[f74])).

fof(f74,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).

fof(f4957,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f138,f1868])).

fof(f1868,plain,
    ( ! [X14,X15] :
        ( ~ r1_tarski(X14,sK7(sK0,X14,a_2_5_lattice3(sK0,X15)))
        | r3_lattices(sK0,k15_lattice3(sK0,X14),k15_lattice3(sK0,X15)) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(resolution,[],[f809,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f809,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f808,f229])).

fof(f808,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f807,f233])).

fof(f807,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f806,f252])).

fof(f806,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f783,f241])).

fof(f783,plain,
    ( ! [X8,X9] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8))
        | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(superposition,[],[f172,f430])).

fof(f430,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f233,f241,f252,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f102])).

fof(f102,plain,(
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

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

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
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(f138,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f863,plain,
    ( ! [X0] : r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f361,f569,f219])).

fof(f219,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f197])).

fof(f197,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X3,X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f120,f121])).

fof(f121,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X2)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK11(X0,X1,X2),X2)
        & sK11(X0,X1,X2) = X0
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f120,plain,(
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
    inference(rectify,[],[f119])).

fof(f119,plain,(
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
    inference(nnf_transformation,[],[f73])).

fof(f73,plain,(
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
    inference(flattening,[],[f72])).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f569,plain,
    ( ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f361,f226])).

fof(f226,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f174])).

fof(f174,plain,(
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
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f106,f107])).

fof(f107,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK8(X0,X1,X2))
        & r4_lattice3(X0,sK8(X0,X1,X2),X1)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
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
    inference(rectify,[],[f105])).

fof(f105,plain,(
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
    inference(flattening,[],[f104])).

fof(f104,plain,(
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
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f1523,plain,
    ( ! [X0] : r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(superposition,[],[f862,f429])).

fof(f429,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f233,f241,f252,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
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
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f862,plain,
    ( ! [X17] : r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f861,f229])).

fof(f861,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f860,f233])).

fof(f860,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f859,f252])).

fof(f859,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f858,f241])).

fof(f858,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f847,f360])).

fof(f360,plain,
    ( ! [X0] : m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f229,f241,f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f847,plain,
    ( ! [X17] :
        ( r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))
        | ~ m1_subset_1(k16_lattice3(sK0,X17),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(superposition,[],[f214,f431])).

fof(f431,plain,
    ( ! [X0] : k16_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f233,f241,f252,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f214,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f99,f100])).

fof(f100,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X0,X3,X1)
          & r3_lattice3(X0,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,sK6(X0,X1,X2),X1)
        & r3_lattice3(X0,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
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
    inference(rectify,[],[f98])).

fof(f98,plain,(
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
    inference(flattening,[],[f97])).

fof(f97,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(flattening,[],[f57])).

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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f412,plain,
    ( v9_lattices(sK0)
    | ~ spl16_7 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl16_7
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f417,plain,
    ( v8_lattices(sK0)
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl16_8
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f9429,plain,
    ( spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | spl16_5
    | ~ spl16_6
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_35
    | ~ spl16_151 ),
    inference(avatar_contradiction_clause,[],[f9428])).

fof(f9428,plain,
    ( $false
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | spl16_5
    | ~ spl16_6
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_35
    | ~ spl16_151 ),
    inference(subsumption_resolution,[],[f9427,f246])).

fof(f246,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl16_5 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl16_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f9427,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_35
    | ~ spl16_151 ),
    inference(forward_demodulation,[],[f9426,f3122])).

fof(f3122,plain,
    ( ! [X0] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_35 ),
    inference(superposition,[],[f1065,f429])).

fof(f1065,plain,
    ( ! [X44] : k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
    | ~ spl16_35 ),
    inference(avatar_component_clause,[],[f1064])).

fof(f1064,plain,
    ( spl16_35
  <=> ! [X44] : k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_35])])).

fof(f9426,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_151 ),
    inference(subsumption_resolution,[],[f9425,f229])).

fof(f9425,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_11
    | ~ spl16_151 ),
    inference(subsumption_resolution,[],[f9424,f417])).

fof(f9424,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_7
    | ~ spl16_11
    | ~ spl16_151 ),
    inference(subsumption_resolution,[],[f9423,f412])).

fof(f9423,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_11
    | ~ spl16_151 ),
    inference(subsumption_resolution,[],[f9422,f241])).

fof(f9422,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_11
    | ~ spl16_151 ),
    inference(subsumption_resolution,[],[f9421,f361])).

fof(f9421,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_11
    | ~ spl16_151 ),
    inference(subsumption_resolution,[],[f9412,f499])).

fof(f499,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl16_11 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl16_11
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f9412,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_151 ),
    inference(resolution,[],[f5392,f144])).

fof(f5392,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl16_151 ),
    inference(avatar_component_clause,[],[f5390])).

fof(f5390,plain,
    ( spl16_151
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_151])])).

fof(f5459,plain,
    ( spl16_151
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_149 ),
    inference(avatar_split_clause,[],[f5458,f5295,f497,f250,f240,f232,f228,f5390])).

fof(f5295,plain,
    ( spl16_149
  <=> r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_149])])).

fof(f5458,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_149 ),
    inference(forward_demodulation,[],[f5457,f429])).

fof(f5457,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_149 ),
    inference(forward_demodulation,[],[f5456,f431])).

fof(f5456,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_149 ),
    inference(subsumption_resolution,[],[f5384,f499])).

fof(f5384,plain,
    ( r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_149 ),
    inference(resolution,[],[f5297,f775])).

fof(f775,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f774,f229])).

fof(f774,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f773,f241])).

fof(f773,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f759,f360])).

fof(f759,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k16_lattice3(sK0,X0),X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(resolution,[],[f501,f179])).

fof(f501,plain,
    ( ! [X0] : r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f360,f214])).

fof(f5297,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | ~ spl16_149 ),
    inference(avatar_component_clause,[],[f5295])).

fof(f5298,plain,
    ( spl16_149
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_124 ),
    inference(avatar_split_clause,[],[f5268,f4998,f497,f250,f240,f232,f228,f5295])).

fof(f4998,plain,
    ( spl16_124
  <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_124])])).

fof(f5268,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11
    | ~ spl16_124 ),
    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f863,f499,f361,f5000,f220])).

fof(f5000,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl16_124 ),
    inference(avatar_component_clause,[],[f4998])).

fof(f5001,plain,
    ( spl16_124
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f4979,f692,f250,f240,f232,f228,f4998])).

fof(f692,plain,
    ( spl16_13
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).

fof(f4979,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(superposition,[],[f4957,f694])).

fof(f694,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ spl16_13 ),
    inference(avatar_component_clause,[],[f692])).

fof(f1066,plain,
    ( ~ spl16_3
    | spl16_35
    | spl16_1
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(avatar_split_clause,[],[f1062,f497,f425,f240,f228,f1064,f236])).

fof(f1062,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ v13_lattices(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f1061,f229])).

fof(f1061,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f1060,f427])).

fof(f1060,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f533,f499])).

fof(f533,plain,
    ( ! [X44] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl16_1
    | ~ spl16_4 ),
    inference(resolution,[],[f360,f211])).

fof(f211,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f84,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
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
    inference(rectify,[],[f83])).

fof(f83,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f723,plain,
    ( spl16_13
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(avatar_split_clause,[],[f722,f497,f250,f240,f232,f228,f692])).

fof(f722,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f721,f229])).

fof(f721,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f720,f233])).

fof(f720,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_4
    | ~ spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f719,f252])).

fof(f719,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f660,f241])).

fof(f660,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_11 ),
    inference(resolution,[],[f499,f163])).

fof(f500,plain,
    ( spl16_11
    | spl16_1
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f481,f425,f228,f497])).

fof(f481,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f229,f427,f146])).

fof(f146,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f428,plain,
    ( spl16_10
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f356,f240,f425])).

fof(f356,plain,
    ( l1_lattices(sK0)
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f241,f139])).

fof(f139,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f423,plain,
    ( spl16_9
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f357,f240,f232,f228,f420])).

fof(f357,plain,
    ( v6_lattices(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f229,f233,f241,f141])).

fof(f141,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f31])).

fof(f31,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
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

fof(f418,plain,
    ( spl16_8
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f358,f240,f232,f228,f415])).

fof(f358,plain,
    ( v8_lattices(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f229,f233,f241,f142])).

fof(f142,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f413,plain,
    ( spl16_7
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f359,f240,f232,f228,f410])).

fof(f359,plain,
    ( v9_lattices(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f229,f233,f241,f143])).

fof(f143,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f255,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f133,f228])).

fof(f133,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f80])).

fof(f80,plain,
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
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

fof(f254,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f134,f232])).

fof(f134,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f253,plain,(
    spl16_6 ),
    inference(avatar_split_clause,[],[f135,f250])).

fof(f135,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f248,plain,(
    spl16_4 ),
    inference(avatar_split_clause,[],[f136,f240])).

fof(f136,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f247,plain,
    ( spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(avatar_split_clause,[],[f137,f244,f240,f236,f232,f228])).

fof(f137,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n025.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 20:27:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.21/0.51  % (18225)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (18220)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (18241)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (18228)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (18228)Refutation not found, incomplete strategy% (18228)------------------------------
% 0.21/0.52  % (18228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18219)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (18228)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18228)Memory used [KB]: 10746
% 0.21/0.53  % (18228)Time elapsed: 0.094 s
% 0.21/0.53  % (18228)------------------------------
% 0.21/0.53  % (18228)------------------------------
% 0.21/0.53  % (18233)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (18223)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (18229)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (18244)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (18222)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (18240)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (18240)Refutation not found, incomplete strategy% (18240)------------------------------
% 0.21/0.54  % (18240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18240)Memory used [KB]: 10874
% 0.21/0.54  % (18240)Time elapsed: 0.082 s
% 0.21/0.54  % (18240)------------------------------
% 0.21/0.54  % (18240)------------------------------
% 0.21/0.54  % (18230)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (18238)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (18221)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (18232)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (18247)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (18246)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (18234)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (18224)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (18218)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (18218)Refutation not found, incomplete strategy% (18218)------------------------------
% 0.21/0.55  % (18218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18218)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18218)Memory used [KB]: 1663
% 0.21/0.55  % (18218)Time elapsed: 0.001 s
% 0.21/0.55  % (18218)------------------------------
% 0.21/0.55  % (18218)------------------------------
% 0.21/0.56  % (18229)Refutation not found, incomplete strategy% (18229)------------------------------
% 0.21/0.56  % (18229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18229)Memory used [KB]: 10746
% 0.21/0.56  % (18229)Time elapsed: 0.131 s
% 0.21/0.56  % (18229)------------------------------
% 0.21/0.56  % (18229)------------------------------
% 0.21/0.56  % (18235)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (18243)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (18227)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (18227)Refutation not found, incomplete strategy% (18227)------------------------------
% 0.21/0.56  % (18227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18242)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (18236)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (18227)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18227)Memory used [KB]: 10618
% 0.21/0.56  % (18227)Time elapsed: 0.003 s
% 0.21/0.56  % (18227)------------------------------
% 0.21/0.56  % (18227)------------------------------
% 0.21/0.56  % (18239)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (18245)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (18231)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (18237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.55/0.57  % (18235)Refutation not found, incomplete strategy% (18235)------------------------------
% 1.55/0.57  % (18235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (18235)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (18235)Memory used [KB]: 10746
% 1.55/0.57  % (18235)Time elapsed: 0.149 s
% 1.55/0.57  % (18235)------------------------------
% 1.55/0.57  % (18235)------------------------------
% 1.55/0.58  % (18226)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.01/0.66  % (18248)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.01/0.68  % (18248)Refutation not found, incomplete strategy% (18248)------------------------------
% 2.01/0.68  % (18248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (18248)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (18248)Memory used [KB]: 6268
% 2.01/0.68  % (18248)Time elapsed: 0.095 s
% 2.01/0.68  % (18248)------------------------------
% 2.01/0.68  % (18248)------------------------------
% 2.01/0.68  % (18253)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.01/0.69  % (18249)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.01/0.69  % (18251)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.01/0.70  % (18250)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.01/0.70  % (18252)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.91/0.81  % (18254)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.54/0.86  % (18223)Time limit reached!
% 3.54/0.86  % (18223)------------------------------
% 3.54/0.86  % (18223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.54/0.86  % (18223)Termination reason: Time limit
% 3.54/0.86  % (18223)Termination phase: Saturation
% 3.54/0.86  
% 3.54/0.86  % (18223)Memory used [KB]: 7164
% 3.54/0.86  % (18223)Time elapsed: 0.400 s
% 3.54/0.86  % (18223)------------------------------
% 3.54/0.86  % (18223)------------------------------
% 3.98/0.93  % (18230)Time limit reached!
% 3.98/0.93  % (18230)------------------------------
% 3.98/0.93  % (18230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.93  % (18230)Termination reason: Time limit
% 3.98/0.93  
% 3.98/0.93  % (18230)Memory used [KB]: 9594
% 3.98/0.93  % (18230)Time elapsed: 0.514 s
% 3.98/0.93  % (18230)------------------------------
% 3.98/0.93  % (18230)------------------------------
% 4.07/0.94  % (18219)Time limit reached!
% 4.07/0.94  % (18219)------------------------------
% 4.07/0.94  % (18219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.94  % (18219)Termination reason: Time limit
% 4.07/0.94  
% 4.07/0.94  % (18219)Memory used [KB]: 9083
% 4.07/0.94  % (18219)Time elapsed: 0.515 s
% 4.07/0.94  % (18219)------------------------------
% 4.07/0.94  % (18219)------------------------------
% 4.07/0.98  % (18255)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.47/1.01  % (18252)Time limit reached!
% 4.47/1.01  % (18252)------------------------------
% 4.47/1.01  % (18252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.01  % (18252)Termination reason: Time limit
% 4.47/1.01  
% 4.47/1.01  % (18252)Memory used [KB]: 12920
% 4.47/1.01  % (18252)Time elapsed: 0.417 s
% 4.47/1.01  % (18252)------------------------------
% 4.47/1.01  % (18252)------------------------------
% 4.47/1.02  % (18251)Time limit reached!
% 4.47/1.02  % (18251)------------------------------
% 4.47/1.02  % (18251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.02  % (18251)Termination reason: Time limit
% 4.47/1.02  
% 4.47/1.02  % (18251)Memory used [KB]: 7547
% 4.47/1.02  % (18251)Time elapsed: 0.421 s
% 4.47/1.03  % (18251)------------------------------
% 4.47/1.03  % (18251)------------------------------
% 4.47/1.05  % (18225)Time limit reached!
% 4.47/1.05  % (18225)------------------------------
% 4.47/1.05  % (18225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.05  % (18225)Termination reason: Time limit
% 4.47/1.05  
% 4.47/1.05  % (18225)Memory used [KB]: 10746
% 4.47/1.05  % (18225)Time elapsed: 0.614 s
% 4.47/1.05  % (18225)------------------------------
% 4.47/1.05  % (18225)------------------------------
% 4.47/1.05  % (18234)Time limit reached!
% 4.47/1.05  % (18234)------------------------------
% 4.47/1.05  % (18234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.05  % (18234)Termination reason: Time limit
% 4.47/1.05  
% 4.47/1.05  % (18234)Memory used [KB]: 17398
% 4.47/1.05  % (18234)Time elapsed: 0.627 s
% 4.47/1.05  % (18234)------------------------------
% 4.47/1.05  % (18234)------------------------------
% 4.47/1.06  % (18257)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.47/1.06  % (18246)Time limit reached!
% 4.47/1.06  % (18246)------------------------------
% 4.47/1.06  % (18246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/1.06  % (18246)Termination reason: Time limit
% 4.47/1.06  
% 4.47/1.06  % (18246)Memory used [KB]: 8059
% 4.47/1.06  % (18246)Time elapsed: 0.644 s
% 4.47/1.06  % (18246)------------------------------
% 4.47/1.06  % (18246)------------------------------
% 4.47/1.07  % (18256)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.51/1.15  % (18259)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.25/1.17  % (18258)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.25/1.19  % (18261)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.25/1.19  % (18260)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.68/1.24  % (18262)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.68/1.24  % (18239)Time limit reached!
% 6.68/1.24  % (18239)------------------------------
% 6.68/1.24  % (18239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.68/1.24  % (18239)Termination reason: Time limit
% 6.68/1.24  
% 6.68/1.24  % (18239)Memory used [KB]: 5117
% 6.68/1.24  % (18239)Time elapsed: 0.819 s
% 6.68/1.24  % (18239)------------------------------
% 6.68/1.24  % (18239)------------------------------
% 7.46/1.38  % (18263)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 7.99/1.43  % (18220)Time limit reached!
% 7.99/1.43  % (18220)------------------------------
% 7.99/1.43  % (18220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.99/1.43  % (18220)Termination reason: Time limit
% 7.99/1.43  
% 7.99/1.43  % (18220)Memory used [KB]: 21108
% 7.99/1.43  % (18220)Time elapsed: 1.006 s
% 7.99/1.43  % (18220)------------------------------
% 7.99/1.43  % (18220)------------------------------
% 9.03/1.57  % (18264)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 9.03/1.61  % (18260)Time limit reached!
% 9.03/1.61  % (18260)------------------------------
% 9.03/1.61  % (18260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.03/1.61  % (18260)Termination reason: Time limit
% 9.03/1.61  
% 9.03/1.61  % (18260)Memory used [KB]: 2814
% 9.03/1.61  % (18260)Time elapsed: 0.523 s
% 9.03/1.61  % (18260)------------------------------
% 9.03/1.61  % (18260)------------------------------
% 9.79/1.64  % (18244)Time limit reached!
% 9.79/1.64  % (18244)------------------------------
% 9.79/1.64  % (18244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.79/1.64  % (18244)Termination reason: Time limit
% 9.79/1.64  % (18244)Termination phase: Saturation
% 9.79/1.64  
% 9.79/1.64  % (18244)Memory used [KB]: 18933
% 9.79/1.64  % (18244)Time elapsed: 1.200 s
% 9.79/1.64  % (18244)------------------------------
% 9.79/1.64  % (18244)------------------------------
% 9.79/1.69  % (18265)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 9.79/1.71  % (18265)Refutation not found, incomplete strategy% (18265)------------------------------
% 9.79/1.71  % (18265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.52/1.71  % (18265)Termination reason: Refutation not found, incomplete strategy
% 10.52/1.71  
% 10.52/1.71  % (18265)Memory used [KB]: 6268
% 10.52/1.71  % (18265)Time elapsed: 0.078 s
% 10.52/1.71  % (18265)------------------------------
% 10.52/1.71  % (18265)------------------------------
% 10.52/1.73  % (18266)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 10.52/1.76  % (18233)Time limit reached!
% 10.52/1.76  % (18233)------------------------------
% 10.52/1.76  % (18233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.52/1.76  % (18233)Termination reason: Time limit
% 10.52/1.76  
% 10.52/1.76  % (18233)Memory used [KB]: 16119
% 10.52/1.76  % (18233)Time elapsed: 1.336 s
% 10.52/1.76  % (18233)------------------------------
% 10.52/1.76  % (18233)------------------------------
% 11.10/1.78  % (18242)Time limit reached!
% 11.10/1.78  % (18242)------------------------------
% 11.10/1.78  % (18242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.10/1.78  % (18242)Termination reason: Time limit
% 11.10/1.78  
% 11.10/1.78  % (18242)Memory used [KB]: 14583
% 11.10/1.78  % (18242)Time elapsed: 1.326 s
% 11.10/1.78  % (18242)------------------------------
% 11.10/1.78  % (18242)------------------------------
% 11.12/1.80  % (18243)Refutation found. Thanks to Tanya!
% 11.12/1.80  % SZS status Theorem for theBenchmark
% 11.12/1.80  % SZS output start Proof for theBenchmark
% 11.29/1.80  fof(f22719,plain,(
% 11.29/1.80    $false),
% 11.29/1.80    inference(avatar_sat_refutation,[],[f247,f248,f253,f254,f255,f413,f418,f423,f428,f500,f723,f1066,f5001,f5298,f5459,f9429,f22718])).
% 11.29/1.80  fof(f22718,plain,(
% 11.29/1.80    spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_9 | ~spl16_10),
% 11.29/1.80    inference(avatar_contradiction_clause,[],[f22717])).
% 11.29/1.80  fof(f22717,plain,(
% 11.29/1.80    $false | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_9 | ~spl16_10)),
% 11.29/1.80    inference(subsumption_resolution,[],[f22686,f570])).
% 11.29/1.80  fof(f570,plain,(
% 11.29/1.80    ( ! [X0] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_10)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f427,f238,f361,f154])).
% 11.29/1.80  fof(f154,plain,(
% 11.29/1.80    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f91])).
% 11.29/1.80  fof(f91,plain,(
% 11.29/1.80    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f88,f90,f89])).
% 11.29/1.80  fof(f89,plain,(
% 11.29/1.80    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f90,plain,(
% 11.29/1.80    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f88,plain,(
% 11.29/1.80    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(rectify,[],[f87])).
% 11.29/1.80  fof(f87,plain,(
% 11.29/1.80    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(nnf_transformation,[],[f46])).
% 11.29/1.80  fof(f46,plain,(
% 11.29/1.80    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f45])).
% 11.29/1.80  fof(f45,plain,(
% 11.29/1.80    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f13])).
% 11.29/1.80  fof(f13,axiom,(
% 11.29/1.80    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 11.29/1.80  fof(f361,plain,(
% 11.29/1.80    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl16_1 | ~spl16_4)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f241,f185])).
% 11.29/1.80  fof(f185,plain,(
% 11.29/1.80    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f68])).
% 11.29/1.80  fof(f68,plain,(
% 11.29/1.80    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f67])).
% 11.29/1.80  fof(f67,plain,(
% 11.29/1.80    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f17])).
% 11.29/1.80  fof(f17,axiom,(
% 11.29/1.80    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 11.29/1.80  fof(f241,plain,(
% 11.29/1.80    l3_lattices(sK0) | ~spl16_4),
% 11.29/1.80    inference(avatar_component_clause,[],[f240])).
% 11.29/1.80  fof(f240,plain,(
% 11.29/1.80    spl16_4 <=> l3_lattices(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 11.29/1.80  fof(f238,plain,(
% 11.29/1.80    ~v13_lattices(sK0) | spl16_3),
% 11.29/1.80    inference(avatar_component_clause,[],[f236])).
% 11.29/1.80  fof(f236,plain,(
% 11.29/1.80    spl16_3 <=> v13_lattices(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).
% 11.29/1.80  fof(f427,plain,(
% 11.29/1.80    l1_lattices(sK0) | ~spl16_10),
% 11.29/1.80    inference(avatar_component_clause,[],[f425])).
% 11.29/1.80  fof(f425,plain,(
% 11.29/1.80    spl16_10 <=> l1_lattices(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).
% 11.29/1.80  fof(f229,plain,(
% 11.29/1.80    ~v2_struct_0(sK0) | spl16_1),
% 11.29/1.80    inference(avatar_component_clause,[],[f228])).
% 11.29/1.80  fof(f228,plain,(
% 11.29/1.80    spl16_1 <=> v2_struct_0(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).
% 11.29/1.80  fof(f22686,plain,(
% 11.29/1.80    ~m1_subset_1(sK2(sK0,k15_lattice3(sK0,k1_xboole_0)),u1_struct_0(sK0)) | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_9 | ~spl16_10)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f417,f412,f241,f361,f10243,f11698,f144])).
% 11.29/1.80  fof(f144,plain,(
% 11.29/1.80    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f82])).
% 11.29/1.80  fof(f82,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(nnf_transformation,[],[f40])).
% 11.29/1.80  fof(f40,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f39])).
% 11.29/1.80  fof(f39,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f12])).
% 11.29/1.80  fof(f12,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 11.29/1.80  fof(f11698,plain,(
% 11.29/1.80    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_9 | ~spl16_10)),
% 11.29/1.80    inference(duplicate_literal_removal,[],[f11694])).
% 11.29/1.80  fof(f11694,plain,(
% 11.29/1.80    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_9 | ~spl16_10)),
% 11.29/1.80    inference(superposition,[],[f622,f1400])).
% 11.29/1.80  fof(f1400,plain,(
% 11.29/1.80    ( ! [X0,X1] : (k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X1))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X1)),k15_lattice3(sK0,X0))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_9 | ~spl16_10)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f427,f422,f361,f570,f156])).
% 11.29/1.80  fof(f156,plain,(
% 11.29/1.80    ( ! [X4,X0,X3] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f96])).
% 11.29/1.80  fof(f96,plain,(
% 11.29/1.80    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f93,f95,f94])).
% 11.29/1.80  fof(f94,plain,(
% 11.29/1.80    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f95,plain,(
% 11.29/1.80    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f93,plain,(
% 11.29/1.80    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(rectify,[],[f92])).
% 11.29/1.80  fof(f92,plain,(
% 11.29/1.80    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(nnf_transformation,[],[f48])).
% 11.29/1.80  fof(f48,plain,(
% 11.29/1.80    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f47])).
% 11.29/1.80  fof(f47,plain,(
% 11.29/1.80    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f16])).
% 11.29/1.80  fof(f16,axiom,(
% 11.29/1.80    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 11.29/1.80  fof(f422,plain,(
% 11.29/1.80    v6_lattices(sK0) | ~spl16_9),
% 11.29/1.80    inference(avatar_component_clause,[],[f420])).
% 11.29/1.80  fof(f420,plain,(
% 11.29/1.80    spl16_9 <=> v6_lattices(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).
% 11.29/1.80  fof(f622,plain,(
% 11.29/1.80    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16)))) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_10)),
% 11.29/1.80    inference(subsumption_resolution,[],[f621,f229])).
% 11.29/1.80  fof(f621,plain,(
% 11.29/1.80    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | v2_struct_0(sK0)) ) | (spl16_1 | spl16_3 | ~spl16_4 | ~spl16_10)),
% 11.29/1.80    inference(subsumption_resolution,[],[f620,f427])).
% 11.29/1.80  fof(f620,plain,(
% 11.29/1.80    ( ! [X16] : (k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | spl16_3 | ~spl16_4)),
% 11.29/1.80    inference(subsumption_resolution,[],[f588,f238])).
% 11.29/1.80  fof(f588,plain,(
% 11.29/1.80    ( ! [X16] : (v13_lattices(sK0) | k15_lattice3(sK0,X16) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X16)),k15_lattice3(sK0,X16)) | k15_lattice3(sK0,X16) != k2_lattices(sK0,k15_lattice3(sK0,X16),sK2(sK0,k15_lattice3(sK0,X16))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4)),
% 11.29/1.80    inference(resolution,[],[f361,f155])).
% 11.29/1.80  fof(f155,plain,(
% 11.29/1.80    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f91])).
% 11.29/1.80  fof(f10243,plain,(
% 11.29/1.80    ( ! [X4] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X4)))) ) | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_10)),
% 11.29/1.80    inference(superposition,[],[f10173,f1411])).
% 11.29/1.80  fof(f1411,plain,(
% 11.29/1.80    ( ! [X0] : (sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,k15_lattice3(sK0,X0))))) ) | (spl16_1 | ~spl16_2 | spl16_3 | ~spl16_4 | ~spl16_6 | ~spl16_10)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f570,f163])).
% 11.29/1.80  fof(f163,plain,(
% 11.29/1.80    ( ! [X0,X1] : (k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f54])).
% 11.29/1.80  fof(f54,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f53])).
% 11.29/1.80  fof(f53,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f25])).
% 11.29/1.80  fof(f25,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).
% 11.29/1.80  fof(f252,plain,(
% 11.29/1.80    v4_lattice3(sK0) | ~spl16_6),
% 11.29/1.80    inference(avatar_component_clause,[],[f250])).
% 11.29/1.80  fof(f250,plain,(
% 11.29/1.80    spl16_6 <=> v4_lattice3(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).
% 11.29/1.80  fof(f233,plain,(
% 11.29/1.80    v10_lattices(sK0) | ~spl16_2),
% 11.29/1.80    inference(avatar_component_clause,[],[f232])).
% 11.29/1.80  fof(f232,plain,(
% 11.29/1.80    spl16_2 <=> v10_lattices(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).
% 11.29/1.80  fof(f10173,plain,(
% 11.29/1.80    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f241,f361,f361,f1523,f4967,f179])).
% 11.29/1.80  fof(f179,plain,(
% 11.29/1.80    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f112])).
% 11.29/1.80  fof(f112,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f110,f111])).
% 11.29/1.80  fof(f111,plain,(
% 11.29/1.80    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f110,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(rectify,[],[f109])).
% 11.29/1.80  fof(f109,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(nnf_transformation,[],[f64])).
% 11.29/1.80  fof(f64,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f63])).
% 11.29/1.80  fof(f63,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f14])).
% 11.29/1.80  fof(f14,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 11.29/1.80  fof(f4967,plain,(
% 11.29/1.80    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f863,f361,f361,f4957,f220])).
% 11.29/1.80  fof(f220,plain,(
% 11.29/1.80    ( ! [X4,X2,X3,X1] : (r2_hidden(X3,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.29/1.80    inference(equality_resolution,[],[f203])).
% 11.29/1.80  fof(f203,plain,(
% 11.29/1.80    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f127])).
% 11.29/1.80  fof(f127,plain,(
% 11.29/1.80    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK13(X0,X1,X2),X2) & r3_lattices(X1,sK13(X0,X1,X2),sK12(X0,X1,X2)) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))) & sK12(X0,X1,X2) = X0 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f124,f126,f125])).
% 11.29/1.80  fof(f125,plain,(
% 11.29/1.80    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK12(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) & sK12(X0,X1,X2) = X0 & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f126,plain,(
% 11.29/1.80    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,sK12(X0,X1,X2)) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK13(X0,X1,X2),X2) & r3_lattices(X1,sK13(X0,X1,X2),sK12(X0,X1,X2)) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f124,plain,(
% 11.29/1.80    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X2) & r3_lattices(X1,X6,X5) & m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(rectify,[],[f123])).
% 11.29/1.80  fof(f123,plain,(
% 11.29/1.80    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_6_lattice3(X1,X2)) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X4,X3) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_6_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(nnf_transformation,[],[f75])).
% 11.29/1.80  fof(f75,plain,(
% 11.29/1.80    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(flattening,[],[f74])).
% 11.29/1.80  fof(f74,plain,(
% 11.29/1.80    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 11.29/1.80    inference(ennf_transformation,[],[f21])).
% 11.29/1.80  fof(f21,axiom,(
% 11.29/1.80    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_6_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_6_lattice3)).
% 11.29/1.80  fof(f4957,plain,(
% 11.29/1.80    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f138,f1868])).
% 11.29/1.80  fof(f1868,plain,(
% 11.29/1.80    ( ! [X14,X15] : (~r1_tarski(X14,sK7(sK0,X14,a_2_5_lattice3(sK0,X15))) | r3_lattices(sK0,k15_lattice3(sK0,X14),k15_lattice3(sK0,X15))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(resolution,[],[f809,f192])).
% 11.29/1.80  fof(f192,plain,(
% 11.29/1.80    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f70])).
% 11.29/1.80  fof(f70,plain,(
% 11.29/1.80    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 11.29/1.80    inference(ennf_transformation,[],[f7])).
% 11.29/1.80  fof(f7,axiom,(
% 11.29/1.80    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 11.29/1.80  fof(f809,plain,(
% 11.29/1.80    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f808,f229])).
% 11.29/1.80  fof(f808,plain,(
% 11.29/1.80    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f807,f233])).
% 11.29/1.80  fof(f807,plain,(
% 11.29/1.80    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f806,f252])).
% 11.29/1.80  fof(f806,plain,(
% 11.29/1.80    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f783,f241])).
% 11.29/1.80  fof(f783,plain,(
% 11.29/1.80    ( ! [X8,X9] : (r3_lattices(sK0,k15_lattice3(sK0,X9),k15_lattice3(sK0,X8)) | r2_hidden(sK7(sK0,X9,a_2_5_lattice3(sK0,X8)),X9) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(superposition,[],[f172,f430])).
% 11.29/1.80  fof(f430,plain,(
% 11.29/1.80    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f241,f252,f161])).
% 11.29/1.80  fof(f161,plain,(
% 11.29/1.80    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f52])).
% 11.29/1.80  fof(f52,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f51])).
% 11.29/1.80  fof(f51,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f26])).
% 11.29/1.80  fof(f26,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).
% 11.29/1.80  fof(f172,plain,(
% 11.29/1.80    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | r2_hidden(sK7(X0,X1,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f103])).
% 11.29/1.80  fof(f103,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f60,f102])).
% 11.29/1.80  fof(f102,plain,(
% 11.29/1.80    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK7(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f60,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f59])).
% 11.29/1.80  fof(f59,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f27])).
% 11.29/1.80  fof(f27,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 11.29/1.80  fof(f138,plain,(
% 11.29/1.80    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f6])).
% 11.29/1.80  fof(f6,axiom,(
% 11.29/1.80    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 11.29/1.80  fof(f863,plain,(
% 11.29/1.80    ( ! [X0] : (r2_hidden(k15_lattice3(sK0,X0),a_2_2_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f361,f569,f219])).
% 11.29/1.80  fof(f219,plain,(
% 11.29/1.80    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.29/1.80    inference(equality_resolution,[],[f197])).
% 11.29/1.80  fof(f197,plain,(
% 11.29/1.80    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f122])).
% 11.29/1.80  fof(f122,plain,(
% 11.29/1.80    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK11(X0,X1,X2),X2) & sK11(X0,X1,X2) = X0 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f120,f121])).
% 11.29/1.80  fof(f121,plain,(
% 11.29/1.80    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK11(X0,X1,X2),X2) & sK11(X0,X1,X2) = X0 & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f120,plain,(
% 11.29/1.80    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X2) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(rectify,[],[f119])).
% 11.29/1.80  fof(f119,plain,(
% 11.29/1.80    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(nnf_transformation,[],[f73])).
% 11.29/1.80  fof(f73,plain,(
% 11.29/1.80    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 11.29/1.80    inference(flattening,[],[f72])).
% 11.29/1.80  fof(f72,plain,(
% 11.29/1.80    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 11.29/1.80    inference(ennf_transformation,[],[f19])).
% 11.29/1.80  fof(f19,axiom,(
% 11.29/1.80    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 11.29/1.80  fof(f569,plain,(
% 11.29/1.80    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f361,f226])).
% 11.29/1.80  fof(f226,plain,(
% 11.29/1.80    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(duplicate_literal_removal,[],[f216])).
% 11.29/1.80  fof(f216,plain,(
% 11.29/1.80    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(equality_resolution,[],[f174])).
% 11.29/1.80  fof(f174,plain,(
% 11.29/1.80    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f108])).
% 11.29/1.80  fof(f108,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f106,f107])).
% 11.29/1.80  fof(f107,plain,(
% 11.29/1.80    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK8(X0,X1,X2)) & r4_lattice3(X0,sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f106,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(rectify,[],[f105])).
% 11.29/1.80  fof(f105,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f104])).
% 11.29/1.80  fof(f104,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(nnf_transformation,[],[f62])).
% 11.29/1.80  fof(f62,plain,(
% 11.29/1.80    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f61])).
% 11.29/1.80  fof(f61,plain,(
% 11.29/1.80    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f15])).
% 11.29/1.80  fof(f15,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 11.29/1.80  fof(f1523,plain,(
% 11.29/1.80    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,X0)))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(superposition,[],[f862,f429])).
% 11.29/1.80  fof(f429,plain,(
% 11.29/1.80    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_2_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f241,f252,f160])).
% 11.29/1.80  fof(f160,plain,(
% 11.29/1.80    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f50])).
% 11.29/1.80  fof(f50,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f49])).
% 11.29/1.80  fof(f49,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f23])).
% 11.29/1.80  fof(f23,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 11.29/1.80  fof(f862,plain,(
% 11.29/1.80    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f861,f229])).
% 11.29/1.80  fof(f861,plain,(
% 11.29/1.80    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f860,f233])).
% 11.29/1.80  fof(f860,plain,(
% 11.29/1.80    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f859,f252])).
% 11.29/1.80  fof(f859,plain,(
% 11.29/1.80    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f858,f241])).
% 11.29/1.80  fof(f858,plain,(
% 11.29/1.80    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f847,f360])).
% 11.29/1.80  fof(f360,plain,(
% 11.29/1.80    ( ! [X0] : (m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl16_1 | ~spl16_4)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f241,f184])).
% 11.29/1.80  fof(f184,plain,(
% 11.29/1.80    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f66])).
% 11.29/1.80  fof(f66,plain,(
% 11.29/1.80    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f65])).
% 11.29/1.80  fof(f65,plain,(
% 11.29/1.80    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f18])).
% 11.29/1.80  fof(f18,axiom,(
% 11.29/1.80    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 11.29/1.80  fof(f847,plain,(
% 11.29/1.80    ( ! [X17] : (r3_lattice3(sK0,k16_lattice3(sK0,X17),a_2_6_lattice3(sK0,X17)) | ~m1_subset_1(k16_lattice3(sK0,X17),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(superposition,[],[f214,f431])).
% 11.29/1.80  fof(f431,plain,(
% 11.29/1.80    ( ! [X0] : (k16_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_6_lattice3(sK0,X0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f241,f252,f162])).
% 11.29/1.80  fof(f162,plain,(
% 11.29/1.80    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f52])).
% 11.29/1.80  fof(f214,plain,(
% 11.29/1.80    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(equality_resolution,[],[f166])).
% 11.29/1.80  fof(f166,plain,(
% 11.29/1.80    ( ! [X2,X0,X1] : (r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f101])).
% 11.29/1.80  fof(f101,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f99,f100])).
% 11.29/1.80  fof(f100,plain,(
% 11.29/1.80    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_lattices(X0,sK6(X0,X1,X2),X1) & r3_lattice3(X0,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f99,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X4] : (r3_lattices(X0,X4,X1) | ~r3_lattice3(X0,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(rectify,[],[f98])).
% 11.29/1.80  fof(f98,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2)) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f97])).
% 11.29/1.80  fof(f97,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | (? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) & ((! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(nnf_transformation,[],[f58])).
% 11.29/1.80  fof(f58,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f57])).
% 11.29/1.80  fof(f57,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f22])).
% 11.29/1.80  fof(f22,axiom,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 11.29/1.80  fof(f412,plain,(
% 11.29/1.80    v9_lattices(sK0) | ~spl16_7),
% 11.29/1.80    inference(avatar_component_clause,[],[f410])).
% 11.29/1.80  fof(f410,plain,(
% 11.29/1.80    spl16_7 <=> v9_lattices(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).
% 11.29/1.80  fof(f417,plain,(
% 11.29/1.80    v8_lattices(sK0) | ~spl16_8),
% 11.29/1.80    inference(avatar_component_clause,[],[f415])).
% 11.29/1.80  fof(f415,plain,(
% 11.29/1.80    spl16_8 <=> v8_lattices(sK0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).
% 11.29/1.80  fof(f9429,plain,(
% 11.29/1.80    spl16_1 | ~spl16_2 | ~spl16_4 | spl16_5 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_35 | ~spl16_151),
% 11.29/1.80    inference(avatar_contradiction_clause,[],[f9428])).
% 11.29/1.80  fof(f9428,plain,(
% 11.29/1.80    $false | (spl16_1 | ~spl16_2 | ~spl16_4 | spl16_5 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_35 | ~spl16_151)),
% 11.29/1.80    inference(subsumption_resolution,[],[f9427,f246])).
% 11.29/1.80  fof(f246,plain,(
% 11.29/1.80    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl16_5),
% 11.29/1.80    inference(avatar_component_clause,[],[f244])).
% 11.29/1.80  fof(f244,plain,(
% 11.29/1.80    spl16_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).
% 11.29/1.80  fof(f9427,plain,(
% 11.29/1.80    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_35 | ~spl16_151)),
% 11.29/1.80    inference(forward_demodulation,[],[f9426,f3122])).
% 11.29/1.80  fof(f3122,plain,(
% 11.29/1.80    ( ! [X0] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_35)),
% 11.29/1.80    inference(superposition,[],[f1065,f429])).
% 11.29/1.80  fof(f1065,plain,(
% 11.29/1.80    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))) ) | ~spl16_35),
% 11.29/1.80    inference(avatar_component_clause,[],[f1064])).
% 11.29/1.80  fof(f1064,plain,(
% 11.29/1.80    spl16_35 <=> ! [X44] : k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0))),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_35])])).
% 11.29/1.80  fof(f9426,plain,(
% 11.29/1.80    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl16_1 | ~spl16_4 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_151)),
% 11.29/1.80    inference(subsumption_resolution,[],[f9425,f229])).
% 11.29/1.80  fof(f9425,plain,(
% 11.29/1.80    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_7 | ~spl16_8 | ~spl16_11 | ~spl16_151)),
% 11.29/1.80    inference(subsumption_resolution,[],[f9424,f417])).
% 11.29/1.80  fof(f9424,plain,(
% 11.29/1.80    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_7 | ~spl16_11 | ~spl16_151)),
% 11.29/1.80    inference(subsumption_resolution,[],[f9423,f412])).
% 11.29/1.80  fof(f9423,plain,(
% 11.29/1.80    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_11 | ~spl16_151)),
% 11.29/1.80    inference(subsumption_resolution,[],[f9422,f241])).
% 11.29/1.80  fof(f9422,plain,(
% 11.29/1.80    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (spl16_1 | ~spl16_4 | ~spl16_11 | ~spl16_151)),
% 11.29/1.80    inference(subsumption_resolution,[],[f9421,f361])).
% 11.29/1.80  fof(f9421,plain,(
% 11.29/1.80    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | (~spl16_11 | ~spl16_151)),
% 11.29/1.80    inference(subsumption_resolution,[],[f9412,f499])).
% 11.29/1.80  fof(f499,plain,(
% 11.29/1.80    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl16_11),
% 11.29/1.80    inference(avatar_component_clause,[],[f497])).
% 11.29/1.80  fof(f497,plain,(
% 11.29/1.80    spl16_11 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).
% 11.29/1.80  fof(f9412,plain,(
% 11.29/1.80    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0) | ~spl16_151),
% 11.29/1.80    inference(resolution,[],[f5392,f144])).
% 11.29/1.80  fof(f5392,plain,(
% 11.29/1.80    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl16_151),
% 11.29/1.80    inference(avatar_component_clause,[],[f5390])).
% 11.29/1.80  fof(f5390,plain,(
% 11.29/1.80    spl16_151 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_151])])).
% 11.29/1.80  fof(f5459,plain,(
% 11.29/1.80    spl16_151 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_149),
% 11.29/1.80    inference(avatar_split_clause,[],[f5458,f5295,f497,f250,f240,f232,f228,f5390])).
% 11.29/1.80  fof(f5295,plain,(
% 11.29/1.80    spl16_149 <=> r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)))),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_149])])).
% 11.29/1.80  fof(f5458,plain,(
% 11.29/1.80    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_149)),
% 11.29/1.80    inference(forward_demodulation,[],[f5457,f429])).
% 11.29/1.80  fof(f5457,plain,(
% 11.29/1.80    r1_lattices(sK0,k16_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0)),k5_lattices(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_149)),
% 11.29/1.80    inference(forward_demodulation,[],[f5456,f431])).
% 11.29/1.80  fof(f5456,plain,(
% 11.29/1.80    r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_149)),
% 11.29/1.80    inference(subsumption_resolution,[],[f5384,f499])).
% 11.29/1.80  fof(f5384,plain,(
% 11.29/1.80    r1_lattices(sK0,k16_lattice3(sK0,a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_149)),
% 11.29/1.80    inference(resolution,[],[f5297,f775])).
% 11.29/1.80  fof(f775,plain,(
% 11.29/1.80    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f774,f229])).
% 11.29/1.80  fof(f774,plain,(
% 11.29/1.80    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f773,f241])).
% 11.29/1.80  fof(f773,plain,(
% 11.29/1.80    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(subsumption_resolution,[],[f759,f360])).
% 11.29/1.80  fof(f759,plain,(
% 11.29/1.80    ( ! [X0,X1] : (r1_lattices(sK0,k16_lattice3(sK0,X0),X1) | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(resolution,[],[f501,f179])).
% 11.29/1.80  fof(f501,plain,(
% 11.29/1.80    ( ! [X0] : (r3_lattice3(sK0,k16_lattice3(sK0,X0),X0)) ) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f360,f214])).
% 11.29/1.80  fof(f5297,plain,(
% 11.29/1.80    r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) | ~spl16_149),
% 11.29/1.80    inference(avatar_component_clause,[],[f5295])).
% 11.29/1.80  fof(f5298,plain,(
% 11.29/1.80    spl16_149 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_124),
% 11.29/1.80    inference(avatar_split_clause,[],[f5268,f4998,f497,f250,f240,f232,f228,f5295])).
% 11.29/1.80  fof(f4998,plain,(
% 11.29/1.80    spl16_124 <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_124])])).
% 11.29/1.80  fof(f5268,plain,(
% 11.29/1.80    r2_hidden(k5_lattices(sK0),a_2_6_lattice3(sK0,a_2_2_lattice3(sK0,k1_xboole_0))) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11 | ~spl16_124)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f252,f241,f863,f499,f361,f5000,f220])).
% 11.29/1.80  fof(f5000,plain,(
% 11.29/1.80    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl16_124),
% 11.29/1.80    inference(avatar_component_clause,[],[f4998])).
% 11.29/1.80  fof(f5001,plain,(
% 11.29/1.80    spl16_124 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_13),
% 11.29/1.80    inference(avatar_split_clause,[],[f4979,f692,f250,f240,f232,f228,f4998])).
% 11.29/1.80  fof(f692,plain,(
% 11.29/1.80    spl16_13 <=> k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0)))),
% 11.29/1.80    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).
% 11.29/1.80  fof(f4979,plain,(
% 11.29/1.80    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_13)),
% 11.29/1.80    inference(superposition,[],[f4957,f694])).
% 11.29/1.80  fof(f694,plain,(
% 11.29/1.80    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~spl16_13),
% 11.29/1.80    inference(avatar_component_clause,[],[f692])).
% 11.29/1.80  fof(f1066,plain,(
% 11.29/1.80    ~spl16_3 | spl16_35 | spl16_1 | ~spl16_4 | ~spl16_10 | ~spl16_11),
% 11.29/1.80    inference(avatar_split_clause,[],[f1062,f497,f425,f240,f228,f1064,f236])).
% 11.29/1.80  fof(f1062,plain,(
% 11.29/1.80    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0)) ) | (spl16_1 | ~spl16_4 | ~spl16_10 | ~spl16_11)),
% 11.29/1.80    inference(subsumption_resolution,[],[f1061,f229])).
% 11.29/1.80  fof(f1061,plain,(
% 11.29/1.80    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4 | ~spl16_10 | ~spl16_11)),
% 11.29/1.80    inference(subsumption_resolution,[],[f1060,f427])).
% 11.29/1.80  fof(f1060,plain,(
% 11.29/1.80    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4 | ~spl16_11)),
% 11.29/1.80    inference(subsumption_resolution,[],[f533,f499])).
% 11.29/1.80  fof(f533,plain,(
% 11.29/1.80    ( ! [X44] : (k5_lattices(sK0) = k2_lattices(sK0,k16_lattice3(sK0,X44),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl16_1 | ~spl16_4)),
% 11.29/1.80    inference(resolution,[],[f360,f211])).
% 11.29/1.80  fof(f211,plain,(
% 11.29/1.80    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(equality_resolution,[],[f148])).
% 11.29/1.80  fof(f148,plain,(
% 11.29/1.80    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f86])).
% 11.29/1.80  fof(f86,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f84,f85])).
% 11.29/1.80  fof(f85,plain,(
% 11.29/1.80    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f84,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(rectify,[],[f83])).
% 11.29/1.80  fof(f83,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(nnf_transformation,[],[f44])).
% 11.29/1.80  fof(f44,plain,(
% 11.29/1.80    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f43])).
% 11.29/1.80  fof(f43,plain,(
% 11.29/1.80    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f9])).
% 11.29/1.80  fof(f9,axiom,(
% 11.29/1.80    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 11.29/1.80  fof(f723,plain,(
% 11.29/1.80    spl16_13 | spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11),
% 11.29/1.80    inference(avatar_split_clause,[],[f722,f497,f250,f240,f232,f228,f692])).
% 11.29/1.80  fof(f722,plain,(
% 11.29/1.80    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | (spl16_1 | ~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11)),
% 11.29/1.80    inference(subsumption_resolution,[],[f721,f229])).
% 11.29/1.80  fof(f721,plain,(
% 11.29/1.80    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl16_2 | ~spl16_4 | ~spl16_6 | ~spl16_11)),
% 11.29/1.80    inference(subsumption_resolution,[],[f720,f233])).
% 11.29/1.80  fof(f720,plain,(
% 11.29/1.80    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl16_4 | ~spl16_6 | ~spl16_11)),
% 11.29/1.80    inference(subsumption_resolution,[],[f719,f252])).
% 11.29/1.80  fof(f719,plain,(
% 11.29/1.80    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl16_4 | ~spl16_11)),
% 11.29/1.80    inference(subsumption_resolution,[],[f660,f241])).
% 11.29/1.80  fof(f660,plain,(
% 11.29/1.80    k5_lattices(sK0) = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl16_11),
% 11.29/1.80    inference(resolution,[],[f499,f163])).
% 11.29/1.80  fof(f500,plain,(
% 11.29/1.80    spl16_11 | spl16_1 | ~spl16_10),
% 11.29/1.80    inference(avatar_split_clause,[],[f481,f425,f228,f497])).
% 11.29/1.80  fof(f481,plain,(
% 11.29/1.80    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl16_1 | ~spl16_10)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f427,f146])).
% 11.29/1.80  fof(f146,plain,(
% 11.29/1.80    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f42])).
% 11.29/1.80  fof(f42,plain,(
% 11.29/1.80    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f41])).
% 11.29/1.80  fof(f41,plain,(
% 11.29/1.80    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f10])).
% 11.29/1.80  fof(f10,axiom,(
% 11.29/1.80    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 11.29/1.80  fof(f428,plain,(
% 11.29/1.80    spl16_10 | ~spl16_4),
% 11.29/1.80    inference(avatar_split_clause,[],[f356,f240,f425])).
% 11.29/1.80  fof(f356,plain,(
% 11.29/1.80    l1_lattices(sK0) | ~spl16_4),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f241,f139])).
% 11.29/1.80  fof(f139,plain,(
% 11.29/1.80    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f36])).
% 11.29/1.80  fof(f36,plain,(
% 11.29/1.80    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 11.29/1.80    inference(ennf_transformation,[],[f30])).
% 11.29/1.80  fof(f30,plain,(
% 11.29/1.80    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 11.29/1.80    inference(pure_predicate_removal,[],[f11])).
% 11.29/1.80  fof(f11,axiom,(
% 11.29/1.80    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 11.29/1.80  fof(f423,plain,(
% 11.29/1.80    spl16_9 | spl16_1 | ~spl16_2 | ~spl16_4),
% 11.29/1.80    inference(avatar_split_clause,[],[f357,f240,f232,f228,f420])).
% 11.29/1.80  fof(f357,plain,(
% 11.29/1.80    v6_lattices(sK0) | (spl16_1 | ~spl16_2 | ~spl16_4)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f241,f141])).
% 11.29/1.80  fof(f141,plain,(
% 11.29/1.80    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f38])).
% 11.29/1.80  fof(f38,plain,(
% 11.29/1.80    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 11.29/1.80    inference(flattening,[],[f37])).
% 11.29/1.80  fof(f37,plain,(
% 11.29/1.80    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 11.29/1.80    inference(ennf_transformation,[],[f33])).
% 11.29/1.80  fof(f33,plain,(
% 11.29/1.80    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 11.29/1.80    inference(pure_predicate_removal,[],[f32])).
% 11.29/1.80  fof(f32,plain,(
% 11.29/1.80    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.29/1.80    inference(pure_predicate_removal,[],[f31])).
% 11.29/1.80  fof(f31,plain,(
% 11.29/1.80    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.29/1.80    inference(pure_predicate_removal,[],[f8])).
% 11.29/1.80  fof(f8,axiom,(
% 11.29/1.80    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 11.29/1.80  fof(f418,plain,(
% 11.29/1.80    spl16_8 | spl16_1 | ~spl16_2 | ~spl16_4),
% 11.29/1.80    inference(avatar_split_clause,[],[f358,f240,f232,f228,f415])).
% 11.29/1.80  fof(f358,plain,(
% 11.29/1.80    v8_lattices(sK0) | (spl16_1 | ~spl16_2 | ~spl16_4)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f241,f142])).
% 11.29/1.80  fof(f142,plain,(
% 11.29/1.80    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f38])).
% 11.29/1.80  fof(f413,plain,(
% 11.29/1.80    spl16_7 | spl16_1 | ~spl16_2 | ~spl16_4),
% 11.29/1.80    inference(avatar_split_clause,[],[f359,f240,f232,f228,f410])).
% 11.29/1.80  fof(f359,plain,(
% 11.29/1.80    v9_lattices(sK0) | (spl16_1 | ~spl16_2 | ~spl16_4)),
% 11.29/1.80    inference(unit_resulting_resolution,[],[f229,f233,f241,f143])).
% 11.29/1.80  fof(f143,plain,(
% 11.29/1.80    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 11.29/1.80    inference(cnf_transformation,[],[f38])).
% 11.29/1.80  fof(f255,plain,(
% 11.29/1.80    ~spl16_1),
% 11.29/1.80    inference(avatar_split_clause,[],[f133,f228])).
% 11.29/1.80  fof(f133,plain,(
% 11.29/1.80    ~v2_struct_0(sK0)),
% 11.29/1.80    inference(cnf_transformation,[],[f81])).
% 11.29/1.80  fof(f81,plain,(
% 11.29/1.80    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 11.29/1.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f80])).
% 11.29/1.80  fof(f80,plain,(
% 11.29/1.80    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 11.29/1.80    introduced(choice_axiom,[])).
% 11.29/1.80  fof(f35,plain,(
% 11.29/1.80    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 11.29/1.80    inference(flattening,[],[f34])).
% 11.29/1.80  fof(f34,plain,(
% 11.29/1.80    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.29/1.80    inference(ennf_transformation,[],[f29])).
% 11.29/1.80  fof(f29,negated_conjecture,(
% 11.29/1.80    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.29/1.80    inference(negated_conjecture,[],[f28])).
% 11.29/1.80  fof(f28,conjecture,(
% 11.29/1.80    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 11.29/1.80    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 11.29/1.80  fof(f254,plain,(
% 11.29/1.80    spl16_2),
% 11.29/1.80    inference(avatar_split_clause,[],[f134,f232])).
% 11.29/1.80  fof(f134,plain,(
% 11.29/1.80    v10_lattices(sK0)),
% 11.29/1.80    inference(cnf_transformation,[],[f81])).
% 11.29/1.80  fof(f253,plain,(
% 11.29/1.80    spl16_6),
% 11.29/1.80    inference(avatar_split_clause,[],[f135,f250])).
% 11.29/1.80  fof(f135,plain,(
% 11.29/1.80    v4_lattice3(sK0)),
% 11.29/1.80    inference(cnf_transformation,[],[f81])).
% 11.29/1.80  fof(f248,plain,(
% 11.29/1.80    spl16_4),
% 11.29/1.80    inference(avatar_split_clause,[],[f136,f240])).
% 11.29/1.80  fof(f136,plain,(
% 11.29/1.80    l3_lattices(sK0)),
% 11.29/1.80    inference(cnf_transformation,[],[f81])).
% 11.29/1.80  fof(f247,plain,(
% 11.29/1.80    spl16_1 | ~spl16_2 | ~spl16_3 | ~spl16_4 | ~spl16_5),
% 11.29/1.80    inference(avatar_split_clause,[],[f137,f244,f240,f236,f232,f228])).
% 11.29/1.80  fof(f137,plain,(
% 11.29/1.80    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 11.29/1.80    inference(cnf_transformation,[],[f81])).
% 11.29/1.80  % SZS output end Proof for theBenchmark
% 11.29/1.80  % (18243)------------------------------
% 11.29/1.80  % (18243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.29/1.80  % (18243)Termination reason: Refutation
% 11.29/1.80  
% 11.29/1.80  % (18243)Memory used [KB]: 19445
% 11.29/1.80  % (18243)Time elapsed: 1.356 s
% 11.29/1.80  % (18243)------------------------------
% 11.29/1.80  % (18243)------------------------------
% 11.29/1.81  % (18217)Success in time 1.418 s
%------------------------------------------------------------------------------
