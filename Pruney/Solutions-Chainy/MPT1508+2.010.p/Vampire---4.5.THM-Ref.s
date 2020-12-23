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
% DateTime   : Thu Dec  3 13:15:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  228 (1016 expanded)
%              Number of leaves         :   34 ( 366 expanded)
%              Depth                    :   22
%              Number of atoms          :  996 (6398 expanded)
%              Number of equality atoms :   65 ( 753 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f321,f1113,f1443,f1468,f1538,f1560,f1620,f1655])).

fof(f1655,plain,
    ( ~ spl23_25
    | spl23_32
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(avatar_contradiction_clause,[],[f1654])).

fof(f1654,plain,
    ( $false
    | ~ spl23_25
    | spl23_32
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(subsumption_resolution,[],[f1651,f1437])).

fof(f1437,plain,
    ( sK15 != k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))
    | spl23_32 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f1436,plain,
    ( spl23_32
  <=> sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_32])])).

fof(f1651,plain,
    ( sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_25
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(resolution,[],[f1648,f262])).

fof(f262,plain,(
    ! [X0] :
      ( ~ sP4(X0,sK14,sK15)
      | sK15 = k15_lattice3(sK14,X0) ) ),
    inference(resolution,[],[f261,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ sP4(X2,X1,X0)
      | k15_lattice3(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP4(X1,X0,X2) )
        & ( sP4(X1,X0,X2)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP5(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP4(X1,X0,X2) )
      | ~ sP5(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f261,plain,(
    ! [X0] : sP5(sK15,sK14,X0) ),
    inference(subsumption_resolution,[],[f260,f88])).

fof(f88,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( sK15 != k16_lattice3(sK14,sK16)
    & r3_lattice3(sK14,sK15,sK16)
    & r2_hidden(sK15,sK16)
    & m1_subset_1(sK15,u1_struct_0(sK14))
    & l3_lattices(sK14)
    & v4_lattice3(sK14)
    & v10_lattices(sK14)
    & ~ v2_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f11,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK14,X2) != X1
              & r3_lattice3(sK14,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK14)) )
      & l3_lattices(sK14)
      & v4_lattice3(sK14)
      & v10_lattices(sK14)
      & ~ v2_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK14,X2) != X1
            & r3_lattice3(sK14,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK14)) )
   => ( ? [X2] :
          ( k16_lattice3(sK14,X2) != sK15
          & r3_lattice3(sK14,sK15,X2)
          & r2_hidden(sK15,X2) )
      & m1_subset_1(sK15,u1_struct_0(sK14)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( k16_lattice3(sK14,X2) != sK15
        & r3_lattice3(sK14,sK15,X2)
        & r2_hidden(sK15,X2) )
   => ( sK15 != k16_lattice3(sK14,sK16)
      & r3_lattice3(sK14,sK15,sK16)
      & r2_hidden(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(f260,plain,(
    ! [X0] :
      ( sP5(sK15,sK14,X0)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f259,f89])).

fof(f89,plain,(
    v10_lattices(sK14) ),
    inference(cnf_transformation,[],[f49])).

fof(f259,plain,(
    ! [X0] :
      ( sP5(sK15,sK14,X0)
      | ~ v10_lattices(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f258,f90])).

fof(f90,plain,(
    v4_lattice3(sK14) ),
    inference(cnf_transformation,[],[f49])).

fof(f258,plain,(
    ! [X0] :
      ( sP5(sK15,sK14,X0)
      | ~ v4_lattice3(sK14)
      | ~ v10_lattices(sK14)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f251,f91])).

fof(f91,plain,(
    l3_lattices(sK14) ),
    inference(cnf_transformation,[],[f49])).

fof(f251,plain,(
    ! [X0] :
      ( sP5(sK15,sK14,X0)
      | ~ l3_lattices(sK14)
      | ~ v4_lattice3(sK14)
      | ~ v10_lattices(sK14)
      | v2_struct_0(sK14) ) ),
    inference(resolution,[],[f150,f92])).

fof(f92,plain,(
    m1_subset_1(sK15,u1_struct_0(sK14)) ),
    inference(cnf_transformation,[],[f49])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP5(X2,X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP5(X2,X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( sP4(X1,X0,X2)
    <=> ( sP3(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f1648,plain,
    ( sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15)
    | ~ spl23_25
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(subsumption_resolution,[],[f1640,f1099])).

fof(f1099,plain,
    ( r2_hidden(sK15,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_25 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f1098,plain,
    ( spl23_25
  <=> r2_hidden(sK15,a_2_1_lattice3(sK14,sK16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_25])])).

fof(f1640,plain,
    ( sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15)
    | ~ r2_hidden(sK15,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(resolution,[],[f1639,f765])).

fof(f765,plain,(
    ! [X2] :
      ( ~ r4_lattice3(sK14,sK15,X2)
      | sP4(X2,sK14,sK15)
      | ~ r2_hidden(sK15,X2) ) ),
    inference(resolution,[],[f759,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X0)
      | sP4(X0,X1,X2)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ~ sP3(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP3(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ~ sP3(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP3(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ~ sP3(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP3(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f759,plain,(
    ! [X0] :
      ( sP3(sK15,sK14,X0)
      | ~ r2_hidden(sK15,X0) ) ),
    inference(subsumption_resolution,[],[f758,f88])).

fof(f758,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK15,X0)
      | sP3(sK15,sK14,X0)
      | v2_struct_0(sK14) ) ),
    inference(subsumption_resolution,[],[f749,f91])).

fof(f749,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK15,X0)
      | sP3(sK15,sK14,X0)
      | ~ l3_lattices(sK14)
      | v2_struct_0(sK14) ) ),
    inference(resolution,[],[f748,f92])).

fof(f748,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | sP3(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f747])).

fof(f747,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP3(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP3(X0,X2,X1) ) ),
    inference(resolution,[],[f745,f154])).

fof(f154,plain,(
    ! [X4,X5,X3] :
      ( sP7(X3,sK18(X4,X3,X5))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | sP3(X4,X3,X5) ) ),
    inference(resolution,[],[f124,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK18(X0,X1,X2))
          & r4_lattice3(X1,sK18(X0,X1,X2),X2)
          & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK18(X0,X1,X2))
        & r4_lattice3(X1,sK18(X0,X1,X2),X2)
        & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP7(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP7(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f35,f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP6(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP6(X1,X0,X2) )
      | ~ sP7(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f745,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X1,sK18(X0,X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f743])).

fof(f743,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP7(X1,sK18(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f276,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK18(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f276,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X0,X3,sK18(X1,X0,X2))
      | sP3(X1,X0,X2)
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP7(X0,sK18(X1,X0,X2)) ) ),
    inference(resolution,[],[f151,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP6(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK19(X0,X1,X2),X0)
          & r2_hidden(sK19(X0,X1,X2),X2)
          & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK19(X0,X1,X2),X0)
        & r2_hidden(sK19(X0,X1,X2),X2)
        & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP6(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X0,X1,X2) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X1,X0,X2] :
      ( ( sP6(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP6(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( sP6(sK18(X0,X1,X2),X1,X2)
      | ~ sP7(X1,sK18(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f118,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK18(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,X1,X2)
      | sP6(X1,X0,X2)
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP6(X1,X0,X2) )
          & ( sP6(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP7(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f1639,plain,
    ( r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(subsumption_resolution,[],[f1638,f157])).

fof(f157,plain,(
    sP7(sK14,sK15) ),
    inference(subsumption_resolution,[],[f156,f88])).

fof(f156,plain,
    ( sP7(sK14,sK15)
    | v2_struct_0(sK14) ),
    inference(subsumption_resolution,[],[f152,f91])).

fof(f152,plain,
    ( sP7(sK14,sK15)
    | ~ l3_lattices(sK14)
    | v2_struct_0(sK14) ),
    inference(resolution,[],[f124,f92])).

fof(f1638,plain,
    ( r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16))
    | ~ sP7(sK14,sK15)
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(resolution,[],[f1634,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1634,plain,
    ( sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(subsumption_resolution,[],[f1633,f93])).

fof(f93,plain,(
    r2_hidden(sK15,sK16) ),
    inference(cnf_transformation,[],[f49])).

fof(f1633,plain,
    ( ~ r2_hidden(sK15,sK16)
    | sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(subsumption_resolution,[],[f1630,f92])).

fof(f1630,plain,
    ( ~ m1_subset_1(sK15,u1_struct_0(sK14))
    | ~ r2_hidden(sK15,sK16)
    | sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(resolution,[],[f1628,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK19(X0,X1,X2),X0)
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f1628,plain,
    ( ! [X0] :
        ( r1_lattices(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ r2_hidden(X0,sK16) )
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(resolution,[],[f1627,f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP8(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK20(X0,X1,X2))
          & r2_hidden(sK20(X0,X1,X2),X2)
          & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f75,f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK20(X0,X1,X2))
        & r2_hidden(sK20(X0,X1,X2),X2)
        & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X1,X0,X2] :
      ( ( sP8(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP8(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( sP8(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f1627,plain,
    ( sP8(sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK14,sK16)
    | ~ spl23_35
    | ~ spl23_41 ),
    inference(subsumption_resolution,[],[f1625,f1537])).

fof(f1537,plain,
    ( sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ spl23_35 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f1535,plain,
    ( spl23_35
  <=> sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_35])])).

fof(f1625,plain,
    ( sP8(sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK14,sK16)
    | ~ sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ spl23_41 ),
    inference(resolution,[],[f1619,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | sP8(X1,X0,X2)
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP8(X1,X0,X2) )
          & ( sP8(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP9(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP8(X1,X0,X2) )
      | ~ sP9(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f1619,plain,
    ( r3_lattice3(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK16)
    | ~ spl23_41 ),
    inference(avatar_component_clause,[],[f1617])).

fof(f1617,plain,
    ( spl23_41
  <=> r3_lattice3(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_41])])).

fof(f1620,plain,
    ( ~ spl23_34
    | spl23_41
    | ~ spl23_33 ),
    inference(avatar_split_clause,[],[f1488,f1440,f1617,f1531])).

fof(f1531,plain,
    ( spl23_34
  <=> sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_34])])).

fof(f1440,plain,
    ( spl23_33
  <=> sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_33])])).

fof(f1488,plain,
    ( r3_lattice3(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK16)
    | ~ sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ spl23_33 ),
    inference(superposition,[],[f143,f1442])).

fof(f1442,plain,
    ( sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ spl23_33 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK22(X0,X1,X2),X0)
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK22(X0,X1,X2),X0)
          & sK22(X0,X1,X2) = X2
          & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f85,f86])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK22(X0,X1,X2),X0)
        & sK22(X0,X1,X2) = X2
        & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(rectify,[],[f84])).

fof(f84,plain,(
    ! [X2,X1,X0] :
      ( ( sP12(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP12(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( sP12(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f1560,plain,
    ( ~ spl23_25
    | spl23_32
    | spl23_34 ),
    inference(avatar_contradiction_clause,[],[f1559])).

fof(f1559,plain,
    ( $false
    | ~ spl23_25
    | spl23_32
    | spl23_34 ),
    inference(subsumption_resolution,[],[f1556,f1437])).

fof(f1556,plain,
    ( sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_25
    | spl23_34 ),
    inference(resolution,[],[f1553,f262])).

fof(f1553,plain,
    ( sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15)
    | ~ spl23_25
    | spl23_34 ),
    inference(subsumption_resolution,[],[f1545,f1099])).

fof(f1545,plain,
    ( sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15)
    | ~ r2_hidden(sK15,a_2_1_lattice3(sK14,sK16))
    | spl23_34 ),
    inference(resolution,[],[f1544,f765])).

fof(f1544,plain,
    ( r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16))
    | spl23_34 ),
    inference(subsumption_resolution,[],[f1543,f157])).

fof(f1543,plain,
    ( r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16))
    | ~ sP7(sK14,sK15)
    | spl23_34 ),
    inference(resolution,[],[f1541,f119])).

fof(f1541,plain,
    ( sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16))
    | spl23_34 ),
    inference(subsumption_resolution,[],[f1540,f88])).

fof(f1540,plain,
    ( sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16))
    | v2_struct_0(sK14)
    | spl23_34 ),
    inference(subsumption_resolution,[],[f1539,f91])).

fof(f1539,plain,
    ( sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16))
    | ~ l3_lattices(sK14)
    | v2_struct_0(sK14)
    | spl23_34 ),
    inference(resolution,[],[f1533,f654])).

fof(f654,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X0,X1,sK19(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP6(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f217,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f44,f43])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP12(X2,X1,X0) )
      | ~ sP13(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP13(sK19(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP12(X0,X1,sK19(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP6(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f139,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK19(X0,X1,X2),X2)
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP12(X2,X1,X0) )
        & ( sP12(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP13(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f1533,plain,
    ( ~ sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | spl23_34 ),
    inference(avatar_component_clause,[],[f1531])).

fof(f1538,plain,
    ( ~ spl23_34
    | spl23_35
    | ~ spl23_33 ),
    inference(avatar_split_clause,[],[f1505,f1440,f1535,f1531])).

fof(f1505,plain,
    ( sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f1504,f88])).

fof(f1504,plain,
    ( sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | v2_struct_0(sK14)
    | ~ spl23_33 ),
    inference(subsumption_resolution,[],[f1489,f91])).

fof(f1489,plain,
    ( sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | ~ l3_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_33 ),
    inference(superposition,[],[f185,f1442])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( sP9(X1,sK22(X0,X1,X2))
      | ~ sP12(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f141,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP9(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP9(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f38,f37])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f1468,plain,
    ( spl23_4
    | ~ spl23_32 ),
    inference(avatar_contradiction_clause,[],[f1467])).

fof(f1467,plain,
    ( $false
    | spl23_4
    | ~ spl23_32 ),
    inference(subsumption_resolution,[],[f1466,f88])).

fof(f1466,plain,
    ( v2_struct_0(sK14)
    | spl23_4
    | ~ spl23_32 ),
    inference(subsumption_resolution,[],[f1465,f313])).

fof(f313,plain,
    ( ~ sP1(sK16,sK14,sK15)
    | spl23_4 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl23_4
  <=> sP1(sK16,sK14,sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_4])])).

fof(f1465,plain,
    ( sP1(sK16,sK14,sK15)
    | v2_struct_0(sK14)
    | ~ spl23_32 ),
    inference(subsumption_resolution,[],[f1464,f91])).

fof(f1464,plain,
    ( ~ l3_lattices(sK14)
    | sP1(sK16,sK14,sK15)
    | v2_struct_0(sK14)
    | ~ spl23_32 ),
    inference(subsumption_resolution,[],[f1463,f90])).

fof(f1463,plain,
    ( ~ v4_lattice3(sK14)
    | ~ l3_lattices(sK14)
    | sP1(sK16,sK14,sK15)
    | v2_struct_0(sK14)
    | ~ spl23_32 ),
    inference(subsumption_resolution,[],[f1462,f89])).

fof(f1462,plain,
    ( ~ v10_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ l3_lattices(sK14)
    | sP1(sK16,sK14,sK15)
    | v2_struct_0(sK14)
    | ~ spl23_32 ),
    inference(subsumption_resolution,[],[f1447,f94])).

fof(f94,plain,(
    r3_lattice3(sK14,sK15,sK16) ),
    inference(cnf_transformation,[],[f49])).

fof(f1447,plain,
    ( ~ r3_lattice3(sK14,sK15,sK16)
    | ~ v10_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ l3_lattices(sK14)
    | sP1(sK16,sK14,sK15)
    | v2_struct_0(sK14)
    | ~ spl23_32 ),
    inference(superposition,[],[f1422,f1438])).

fof(f1438,plain,
    ( sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_32 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f1422,plain,(
    ! [X4,X3] :
      ( ~ r3_lattice3(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X4)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ l3_lattices(X3)
      | sP1(X4,X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)))
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f1420,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | sP1(X0,X1,X2)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ( sP0(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1420,plain,(
    ! [X0,X1] :
      ( sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f1419])).

fof(f1419,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f1102,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( sP12(X0,X1,sK17(X2,X1,X0))
      | sP0(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f199,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK17(X0,X1,X2),X0)
          & r3_lattice3(X1,sK17(X0,X1,X2),X2)
          & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK17(X0,X1,X2),X0)
        & r3_lattice3(X1,sK17(X0,X1,X2),X2)
        & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( sP12(X0,X1,sK17(X2,X1,X0))
      | ~ m1_subset_1(sK17(X2,X1,X0),u1_struct_0(X1))
      | sP0(X2,X1,X0) ) ),
    inference(resolution,[],[f149,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK17(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f149,plain,(
    ! [X0,X3,X1] :
      ( ~ r3_lattice3(X1,X3,X0)
      | sP12(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f144])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f1102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP12(X2,X1,sK17(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f416,f145])).

fof(f416,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP13(sK17(k15_lattice3(X4,a_2_1_lattice3(X5,X6)),X4,X7),X5,X6)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | sP0(k15_lattice3(X4,a_2_1_lattice3(X5,X6)),X4,X7)
      | ~ sP12(X6,X5,sK17(k15_lattice3(X4,a_2_1_lattice3(X5,X6)),X4,X7))
      | ~ l3_lattices(X4) ) ),
    inference(resolution,[],[f283,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK17(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f282,f104])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK17(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ m1_subset_1(sK17(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f96,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK17(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f1443,plain,
    ( spl23_32
    | spl23_33
    | ~ spl23_25 ),
    inference(avatar_split_clause,[],[f1433,f1098,f1440,f1436])).

fof(f1433,plain,
    ( sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_25 ),
    inference(subsumption_resolution,[],[f1432,f88])).

fof(f1432,plain,
    ( v2_struct_0(sK14)
    | sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_25 ),
    inference(subsumption_resolution,[],[f1430,f91])).

fof(f1430,plain,
    ( ~ l3_lattices(sK14)
    | v2_struct_0(sK14)
    | sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))
    | sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))
    | ~ spl23_25 ),
    inference(resolution,[],[f1273,f1099])).

fof(f1273,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK15,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sK19(sK15,sK14,a_2_1_lattice3(X0,X1)) = sK22(X1,X0,sK19(sK15,sK14,a_2_1_lattice3(X0,X1)))
      | sK15 = k15_lattice3(sK14,a_2_1_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f995,f262])).

fof(f995,plain,(
    ! [X54,X55] :
      ( sP4(a_2_1_lattice3(X54,X55),sK14,sK15)
      | sK19(sK15,sK14,a_2_1_lattice3(X54,X55)) = sK22(X55,X54,sK19(sK15,sK14,a_2_1_lattice3(X54,X55)))
      | ~ l3_lattices(X54)
      | v2_struct_0(X54)
      | ~ r2_hidden(sK15,a_2_1_lattice3(X54,X55)) ) ),
    inference(subsumption_resolution,[],[f982,f157])).

fof(f982,plain,(
    ! [X54,X55] :
      ( v2_struct_0(X54)
      | sK19(sK15,sK14,a_2_1_lattice3(X54,X55)) = sK22(X55,X54,sK19(sK15,sK14,a_2_1_lattice3(X54,X55)))
      | ~ l3_lattices(X54)
      | ~ sP7(sK14,sK15)
      | sP4(a_2_1_lattice3(X54,X55),sK14,sK15)
      | ~ r2_hidden(sK15,a_2_1_lattice3(X54,X55)) ) ),
    inference(resolution,[],[f841,f765])).

fof(f841,plain,(
    ! [X6,X8,X7,X5] :
      ( r4_lattice3(X7,X6,a_2_1_lattice3(X5,X8))
      | v2_struct_0(X5)
      | sK19(X6,X7,a_2_1_lattice3(X5,X8)) = sK22(X8,X5,sK19(X6,X7,a_2_1_lattice3(X5,X8)))
      | ~ l3_lattices(X5)
      | ~ sP7(X7,X6) ) ),
    inference(resolution,[],[f727,f119])).

fof(f727,plain,(
    ! [X10,X8,X11,X9] :
      ( sP6(X8,X9,a_2_1_lattice3(X10,X11))
      | ~ l3_lattices(X10)
      | v2_struct_0(X10)
      | sK19(X8,X9,a_2_1_lattice3(X10,X11)) = sK22(X11,X10,sK19(X8,X9,a_2_1_lattice3(X10,X11))) ) ),
    inference(resolution,[],[f654,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ sP12(X0,X1,X2)
      | sK22(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f87])).

fof(f1113,plain,(
    spl23_25 ),
    inference(avatar_contradiction_clause,[],[f1112])).

fof(f1112,plain,
    ( $false
    | spl23_25 ),
    inference(subsumption_resolution,[],[f1111,f88])).

fof(f1111,plain,
    ( v2_struct_0(sK14)
    | spl23_25 ),
    inference(subsumption_resolution,[],[f1110,f91])).

fof(f1110,plain,
    ( ~ l3_lattices(sK14)
    | v2_struct_0(sK14)
    | spl23_25 ),
    inference(resolution,[],[f1109,f145])).

fof(f1109,plain,
    ( ~ sP13(sK15,sK14,sK16)
    | spl23_25 ),
    inference(subsumption_resolution,[],[f1108,f202])).

fof(f202,plain,(
    sP12(sK16,sK14,sK15) ),
    inference(subsumption_resolution,[],[f198,f92])).

fof(f198,plain,
    ( sP12(sK16,sK14,sK15)
    | ~ m1_subset_1(sK15,u1_struct_0(sK14)) ),
    inference(resolution,[],[f149,f94])).

fof(f1108,plain,
    ( ~ sP12(sK16,sK14,sK15)
    | ~ sP13(sK15,sK14,sK16)
    | spl23_25 ),
    inference(resolution,[],[f1100,f140])).

fof(f1100,plain,
    ( ~ r2_hidden(sK15,a_2_1_lattice3(sK14,sK16))
    | spl23_25 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f321,plain,(
    ~ spl23_4 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl23_4 ),
    inference(subsumption_resolution,[],[f319,f233])).

fof(f233,plain,(
    sP2(sK15,sK14) ),
    inference(subsumption_resolution,[],[f232,f88])).

fof(f232,plain,
    ( sP2(sK15,sK14)
    | v2_struct_0(sK14) ),
    inference(subsumption_resolution,[],[f231,f89])).

fof(f231,plain,
    ( sP2(sK15,sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14) ),
    inference(subsumption_resolution,[],[f230,f90])).

fof(f230,plain,
    ( sP2(sK15,sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14) ),
    inference(subsumption_resolution,[],[f223,f91])).

fof(f223,plain,
    ( sP2(sK15,sK14)
    | ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14) ),
    inference(resolution,[],[f107,f92])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f28,f27,f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f319,plain,
    ( ~ sP2(sK15,sK14)
    | ~ spl23_4 ),
    inference(subsumption_resolution,[],[f316,f95])).

fof(f95,plain,(
    sK15 != k16_lattice3(sK14,sK16) ),
    inference(cnf_transformation,[],[f49])).

fof(f316,plain,
    ( sK15 = k16_lattice3(sK14,sK16)
    | ~ sP2(sK15,sK14)
    | ~ spl23_4 ),
    inference(resolution,[],[f314,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X2,X1,X0)
      | k16_lattice3(X1,X2) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP1(X2,X1,X0) )
          & ( sP1(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP1(X2,X0,X1) )
          & ( sP1(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f314,plain,
    ( sP1(sK16,sK14,sK15)
    | ~ spl23_4 ),
    inference(avatar_component_clause,[],[f312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:00:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.49  % (28525)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.50  % (28505)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.50  % (28511)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.51  % (28530)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.51  % (28516)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.51  % (28528)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.51  % (28517)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.51  % (28519)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.51  % (28516)Refutation not found, incomplete strategy% (28516)------------------------------
% 0.23/0.51  % (28516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (28516)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (28516)Memory used [KB]: 10490
% 0.23/0.51  % (28516)Time elapsed: 0.080 s
% 0.23/0.51  % (28516)------------------------------
% 0.23/0.51  % (28516)------------------------------
% 0.23/0.51  % (28505)Refutation not found, incomplete strategy% (28505)------------------------------
% 0.23/0.51  % (28505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (28505)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (28505)Memory used [KB]: 10490
% 0.23/0.52  % (28505)Time elapsed: 0.086 s
% 0.23/0.52  % (28505)------------------------------
% 0.23/0.52  % (28505)------------------------------
% 0.23/0.52  % (28512)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.52  % (28508)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.52  % (28512)Refutation not found, incomplete strategy% (28512)------------------------------
% 0.23/0.52  % (28512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (28512)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (28512)Memory used [KB]: 1663
% 0.23/0.52  % (28512)Time elapsed: 0.085 s
% 0.23/0.52  % (28512)------------------------------
% 0.23/0.52  % (28512)------------------------------
% 0.23/0.52  % (28520)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.52  % (28510)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.52  % (28511)Refutation not found, incomplete strategy% (28511)------------------------------
% 0.23/0.52  % (28511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (28511)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (28511)Memory used [KB]: 10618
% 0.23/0.52  % (28511)Time elapsed: 0.084 s
% 0.23/0.52  % (28511)------------------------------
% 0.23/0.52  % (28511)------------------------------
% 0.23/0.52  % (28515)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.52  % (28513)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.52  % (28527)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.53  % (28509)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.53  % (28506)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.53  % (28521)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.53  % (28526)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (28523)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.53  % (28529)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.53  % (28518)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.53  % (28524)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.53  % (28518)Refutation not found, incomplete strategy% (28518)------------------------------
% 0.23/0.53  % (28518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (28518)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (28518)Memory used [KB]: 6140
% 0.23/0.53  % (28518)Time elapsed: 0.110 s
% 0.23/0.53  % (28518)------------------------------
% 0.23/0.53  % (28518)------------------------------
% 0.23/0.54  % (28514)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.55  % (28507)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.55  % (28530)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f1656,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f321,f1113,f1443,f1468,f1538,f1560,f1620,f1655])).
% 0.23/0.55  fof(f1655,plain,(
% 0.23/0.55    ~spl23_25 | spl23_32 | ~spl23_35 | ~spl23_41),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f1654])).
% 0.23/0.55  fof(f1654,plain,(
% 0.23/0.55    $false | (~spl23_25 | spl23_32 | ~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1651,f1437])).
% 0.23/0.55  fof(f1437,plain,(
% 0.23/0.55    sK15 != k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) | spl23_32),
% 0.23/0.55    inference(avatar_component_clause,[],[f1436])).
% 0.23/0.55  fof(f1436,plain,(
% 0.23/0.55    spl23_32 <=> sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl23_32])])).
% 0.23/0.55  fof(f1651,plain,(
% 0.23/0.55    sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) | (~spl23_25 | ~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(resolution,[],[f1648,f262])).
% 0.23/0.55  fof(f262,plain,(
% 0.23/0.55    ( ! [X0] : (~sP4(X0,sK14,sK15) | sK15 = k15_lattice3(sK14,X0)) )),
% 0.23/0.55    inference(resolution,[],[f261,f109])).
% 0.23/0.55  fof(f109,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | k15_lattice3(X1,X2) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f60])).
% 0.23/0.55  fof(f60,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP5(X0,X1,X2))),
% 0.23/0.55    inference(rectify,[],[f59])).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP4(X1,X0,X2)) & (sP4(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP5(X2,X0,X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f32])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP4(X1,X0,X2)) | ~sP5(X2,X0,X1))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.23/0.55  fof(f261,plain,(
% 0.23/0.55    ( ! [X0] : (sP5(sK15,sK14,X0)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f260,f88])).
% 0.23/0.55  fof(f88,plain,(
% 0.23/0.55    ~v2_struct_0(sK14)),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f49,plain,(
% 0.23/0.55    ((sK15 != k16_lattice3(sK14,sK16) & r3_lattice3(sK14,sK15,sK16) & r2_hidden(sK15,sK16)) & m1_subset_1(sK15,u1_struct_0(sK14))) & l3_lattices(sK14) & v4_lattice3(sK14) & v10_lattices(sK14) & ~v2_struct_0(sK14)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15,sK16])],[f11,f48,f47,f46])).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK14,X2) != X1 & r3_lattice3(sK14,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK14))) & l3_lattices(sK14) & v4_lattice3(sK14) & v10_lattices(sK14) & ~v2_struct_0(sK14))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f47,plain,(
% 0.23/0.55    ? [X1] : (? [X2] : (k16_lattice3(sK14,X2) != X1 & r3_lattice3(sK14,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK14))) => (? [X2] : (k16_lattice3(sK14,X2) != sK15 & r3_lattice3(sK14,sK15,X2) & r2_hidden(sK15,X2)) & m1_subset_1(sK15,u1_struct_0(sK14)))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f48,plain,(
% 0.23/0.55    ? [X2] : (k16_lattice3(sK14,X2) != sK15 & r3_lattice3(sK14,sK15,X2) & r2_hidden(sK15,X2)) => (sK15 != k16_lattice3(sK14,sK16) & r3_lattice3(sK14,sK15,sK16) & r2_hidden(sK15,sK16))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f11,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.23/0.55    inference(flattening,[],[f10])).
% 0.23/0.55  fof(f10,plain,(
% 0.23/0.55    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,negated_conjecture,(
% 0.23/0.55    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.23/0.55    inference(negated_conjecture,[],[f8])).
% 0.23/0.55  fof(f8,conjecture,(
% 0.23/0.55    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 0.23/0.55  fof(f260,plain,(
% 0.23/0.55    ( ! [X0] : (sP5(sK15,sK14,X0) | v2_struct_0(sK14)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f259,f89])).
% 0.23/0.55  fof(f89,plain,(
% 0.23/0.55    v10_lattices(sK14)),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f259,plain,(
% 0.23/0.55    ( ! [X0] : (sP5(sK15,sK14,X0) | ~v10_lattices(sK14) | v2_struct_0(sK14)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f258,f90])).
% 0.23/0.55  fof(f90,plain,(
% 0.23/0.55    v4_lattice3(sK14)),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f258,plain,(
% 0.23/0.55    ( ! [X0] : (sP5(sK15,sK14,X0) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f251,f91])).
% 0.23/0.55  fof(f91,plain,(
% 0.23/0.55    l3_lattices(sK14)),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f251,plain,(
% 0.23/0.55    ( ! [X0] : (sP5(sK15,sK14,X0) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) )),
% 0.23/0.55    inference(resolution,[],[f150,f92])).
% 0.23/0.55  fof(f92,plain,(
% 0.23/0.55    m1_subset_1(sK15,u1_struct_0(sK14))),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f150,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP5(X2,X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.23/0.55    inference(duplicate_literal_removal,[],[f117])).
% 0.23/0.55  fof(f117,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f33])).
% 0.23/0.55  fof(f33,plain,(
% 0.23/0.55    ! [X0] : (! [X1,X2] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(definition_folding,[],[f17,f32,f31,f30])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ! [X2,X0,X1] : (sP3(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.23/0.55  fof(f31,plain,(
% 0.23/0.55    ! [X1,X0,X2] : (sP4(X1,X0,X2) <=> (sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.23/0.55  fof(f17,plain,(
% 0.23/0.55    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(flattening,[],[f16])).
% 0.23/0.55  fof(f16,plain,(
% 0.23/0.55    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f3])).
% 0.23/0.55  fof(f3,axiom,(
% 0.23/0.55    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 0.23/0.55  fof(f1648,plain,(
% 0.23/0.55    sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15) | (~spl23_25 | ~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1640,f1099])).
% 0.23/0.55  fof(f1099,plain,(
% 0.23/0.55    r2_hidden(sK15,a_2_1_lattice3(sK14,sK16)) | ~spl23_25),
% 0.23/0.55    inference(avatar_component_clause,[],[f1098])).
% 0.23/0.55  fof(f1098,plain,(
% 0.23/0.55    spl23_25 <=> r2_hidden(sK15,a_2_1_lattice3(sK14,sK16))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl23_25])])).
% 0.23/0.55  fof(f1640,plain,(
% 0.23/0.55    sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15) | ~r2_hidden(sK15,a_2_1_lattice3(sK14,sK16)) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(resolution,[],[f1639,f765])).
% 0.23/0.55  fof(f765,plain,(
% 0.23/0.55    ( ! [X2] : (~r4_lattice3(sK14,sK15,X2) | sP4(X2,sK14,sK15) | ~r2_hidden(sK15,X2)) )),
% 0.23/0.55    inference(resolution,[],[f759,f112])).
% 0.23/0.55  fof(f112,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~sP3(X2,X1,X0) | sP4(X0,X1,X2) | ~r4_lattice3(X1,X2,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f63])).
% 0.23/0.55  fof(f63,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ~sP3(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP3(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP4(X0,X1,X2)))),
% 0.23/0.55    inference(rectify,[],[f62])).
% 0.23/0.55  fof(f62,plain,(
% 0.23/0.55    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | ~sP3(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP4(X1,X0,X2)))),
% 0.23/0.55    inference(flattening,[],[f61])).
% 0.23/0.55  fof(f61,plain,(
% 0.23/0.55    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | (~sP3(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP4(X1,X0,X2)))),
% 0.23/0.55    inference(nnf_transformation,[],[f31])).
% 0.23/0.55  fof(f759,plain,(
% 0.23/0.55    ( ! [X0] : (sP3(sK15,sK14,X0) | ~r2_hidden(sK15,X0)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f758,f88])).
% 0.23/0.55  fof(f758,plain,(
% 0.23/0.55    ( ! [X0] : (~r2_hidden(sK15,X0) | sP3(sK15,sK14,X0) | v2_struct_0(sK14)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f749,f91])).
% 0.23/0.55  fof(f749,plain,(
% 0.23/0.55    ( ! [X0] : (~r2_hidden(sK15,X0) | sP3(sK15,sK14,X0) | ~l3_lattices(sK14) | v2_struct_0(sK14)) )),
% 0.23/0.55    inference(resolution,[],[f748,f92])).
% 0.23/0.55  fof(f748,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | sP3(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 0.23/0.55    inference(duplicate_literal_removal,[],[f747])).
% 0.23/0.55  fof(f747,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP3(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | sP3(X0,X2,X1)) )),
% 0.23/0.55    inference(resolution,[],[f745,f154])).
% 0.23/0.55  fof(f154,plain,(
% 0.23/0.55    ( ! [X4,X5,X3] : (sP7(X3,sK18(X4,X3,X5)) | ~l3_lattices(X3) | v2_struct_0(X3) | sP3(X4,X3,X5)) )),
% 0.23/0.55    inference(resolution,[],[f124,f114])).
% 0.23/0.55  fof(f114,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f67])).
% 0.23/0.55  fof(f67,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,X0,sK18(X0,X1,X2)) & r4_lattice3(X1,sK18(X0,X1,X2),X2) & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f65,f66])).
% 0.23/0.55  fof(f66,plain,(
% 0.23/0.55    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK18(X0,X1,X2)) & r4_lattice3(X1,sK18(X0,X1,X2),X2) & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f65,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.23/0.55    inference(rectify,[],[f64])).
% 0.23/0.55  fof(f64,plain,(
% 0.23/0.55    ! [X2,X0,X1] : ((sP3(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X2,X0,X1)))),
% 0.23/0.55    inference(nnf_transformation,[],[f30])).
% 0.23/0.55  fof(f124,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP7(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f36])).
% 0.23/0.55  fof(f36,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (sP7(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(definition_folding,[],[f19,f35,f34])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    ! [X1,X0,X2] : (sP6(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP6(X1,X0,X2)) | ~sP7(X0,X1))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(flattening,[],[f18])).
% 0.23/0.55  fof(f18,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 0.23/0.55  fof(f745,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~sP7(X1,sK18(X0,X1,X2)) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 0.23/0.55    inference(duplicate_literal_removal,[],[f743])).
% 0.23/0.55  fof(f743,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~sP7(X1,sK18(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 0.23/0.55    inference(resolution,[],[f276,f116])).
% 0.23/0.55  fof(f116,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK18(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f67])).
% 0.23/0.55  fof(f276,plain,(
% 0.23/0.55    ( ! [X2,X0,X3,X1] : (r1_lattices(X0,X3,sK18(X1,X0,X2)) | sP3(X1,X0,X2) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~sP7(X0,sK18(X1,X0,X2))) )),
% 0.23/0.55    inference(resolution,[],[f151,f120])).
% 0.23/0.55  fof(f120,plain,(
% 0.23/0.55    ( ! [X4,X2,X0,X1] : (~sP6(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f72])).
% 0.23/0.55  fof(f72,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | (~r1_lattices(X1,sK19(X0,X1,X2),X0) & r2_hidden(sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f70,f71])).
% 0.23/0.55  fof(f71,plain,(
% 0.23/0.55    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK19(X0,X1,X2),X0) & r2_hidden(sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f70,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 0.23/0.55    inference(rectify,[],[f69])).
% 0.23/0.55  fof(f69,plain,(
% 0.23/0.55    ! [X1,X0,X2] : ((sP6(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP6(X1,X0,X2)))),
% 0.23/0.55    inference(nnf_transformation,[],[f34])).
% 0.23/0.55  fof(f151,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (sP6(sK18(X0,X1,X2),X1,X2) | ~sP7(X1,sK18(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 0.23/0.55    inference(resolution,[],[f118,f115])).
% 0.23/0.55  fof(f115,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK18(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f67])).
% 0.23/0.55  fof(f118,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r4_lattice3(X0,X1,X2) | sP6(X1,X0,X2) | ~sP7(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f68])).
% 0.23/0.55  fof(f68,plain,(
% 0.23/0.55    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP6(X1,X0,X2)) & (sP6(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP7(X0,X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f35])).
% 0.23/0.55  fof(f1639,plain,(
% 0.23/0.55    r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16)) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1638,f157])).
% 0.23/0.55  fof(f157,plain,(
% 0.23/0.55    sP7(sK14,sK15)),
% 0.23/0.55    inference(subsumption_resolution,[],[f156,f88])).
% 0.23/0.55  fof(f156,plain,(
% 0.23/0.55    sP7(sK14,sK15) | v2_struct_0(sK14)),
% 0.23/0.55    inference(subsumption_resolution,[],[f152,f91])).
% 0.23/0.55  fof(f152,plain,(
% 0.23/0.55    sP7(sK14,sK15) | ~l3_lattices(sK14) | v2_struct_0(sK14)),
% 0.23/0.55    inference(resolution,[],[f124,f92])).
% 0.23/0.55  fof(f1638,plain,(
% 0.23/0.55    r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16)) | ~sP7(sK14,sK15) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(resolution,[],[f1634,f119])).
% 0.23/0.55  fof(f119,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~sP6(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP7(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f68])).
% 0.23/0.55  fof(f1634,plain,(
% 0.23/0.55    sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16)) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1633,f93])).
% 0.23/0.55  fof(f93,plain,(
% 0.23/0.55    r2_hidden(sK15,sK16)),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f1633,plain,(
% 0.23/0.55    ~r2_hidden(sK15,sK16) | sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16)) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1630,f92])).
% 0.23/0.55  fof(f1630,plain,(
% 0.23/0.55    ~m1_subset_1(sK15,u1_struct_0(sK14)) | ~r2_hidden(sK15,sK16) | sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16)) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(resolution,[],[f1628,f123])).
% 0.23/0.55  fof(f123,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK19(X0,X1,X2),X0) | sP6(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f72])).
% 0.23/0.55  fof(f1628,plain,(
% 0.23/0.55    ( ! [X0] : (r1_lattices(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~r2_hidden(X0,sK16)) ) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(resolution,[],[f1627,f127])).
% 0.23/0.55  fof(f127,plain,(
% 0.23/0.55    ( ! [X4,X2,X0,X1] : (~sP8(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f77])).
% 0.23/0.55  fof(f77,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | (~r1_lattices(X1,X0,sK20(X0,X1,X2)) & r2_hidden(sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f75,f76])).
% 0.23/0.55  fof(f76,plain,(
% 0.23/0.55    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK20(X0,X1,X2)) & r2_hidden(sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f75,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 0.23/0.55    inference(rectify,[],[f74])).
% 0.23/0.55  fof(f74,plain,(
% 0.23/0.55    ! [X1,X0,X2] : ((sP8(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP8(X1,X0,X2)))),
% 0.23/0.55    inference(nnf_transformation,[],[f37])).
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    ! [X1,X0,X2] : (sP8(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.23/0.55  fof(f1627,plain,(
% 0.23/0.55    sP8(sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK14,sK16) | (~spl23_35 | ~spl23_41)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1625,f1537])).
% 0.23/0.55  fof(f1537,plain,(
% 0.23/0.55    sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~spl23_35),
% 0.23/0.55    inference(avatar_component_clause,[],[f1535])).
% 0.23/0.55  fof(f1535,plain,(
% 0.23/0.55    spl23_35 <=> sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl23_35])])).
% 0.23/0.55  fof(f1625,plain,(
% 0.23/0.55    sP8(sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK14,sK16) | ~sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~spl23_41),
% 0.23/0.55    inference(resolution,[],[f1619,f125])).
% 0.23/0.55  fof(f125,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r3_lattice3(X0,X1,X2) | sP8(X1,X0,X2) | ~sP9(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f73])).
% 0.23/0.55  fof(f73,plain,(
% 0.23/0.55    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP8(X1,X0,X2)) & (sP8(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP9(X0,X1))),
% 0.23/0.55    inference(nnf_transformation,[],[f38])).
% 0.23/0.55  fof(f38,plain,(
% 0.23/0.55    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP8(X1,X0,X2)) | ~sP9(X0,X1))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 0.23/0.55  fof(f1619,plain,(
% 0.23/0.55    r3_lattice3(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK16) | ~spl23_41),
% 0.23/0.55    inference(avatar_component_clause,[],[f1617])).
% 0.23/0.55  fof(f1617,plain,(
% 0.23/0.55    spl23_41 <=> r3_lattice3(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK16)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl23_41])])).
% 0.23/0.55  fof(f1620,plain,(
% 0.23/0.55    ~spl23_34 | spl23_41 | ~spl23_33),
% 0.23/0.55    inference(avatar_split_clause,[],[f1488,f1440,f1617,f1531])).
% 0.23/0.55  fof(f1531,plain,(
% 0.23/0.55    spl23_34 <=> sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl23_34])])).
% 0.23/0.55  fof(f1440,plain,(
% 0.23/0.55    spl23_33 <=> sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl23_33])])).
% 0.23/0.55  fof(f1488,plain,(
% 0.23/0.55    r3_lattice3(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)),sK16) | ~sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~spl23_33),
% 0.23/0.55    inference(superposition,[],[f143,f1442])).
% 0.23/0.55  fof(f1442,plain,(
% 0.23/0.55    sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~spl23_33),
% 0.23/0.55    inference(avatar_component_clause,[],[f1440])).
% 0.23/0.55  fof(f143,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK22(X0,X1,X2),X0) | ~sP12(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f87])).
% 0.23/0.55  fof(f87,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f85,f86])).
% 0.23/0.55  fof(f86,plain,(
% 0.23/0.55    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f85,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 0.23/0.55    inference(rectify,[],[f84])).
% 0.23/0.55  fof(f84,plain,(
% 0.23/0.55    ! [X2,X1,X0] : ((sP12(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP12(X2,X1,X0)))),
% 0.23/0.55    inference(nnf_transformation,[],[f43])).
% 0.23/0.55  fof(f43,plain,(
% 0.23/0.55    ! [X2,X1,X0] : (sP12(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).
% 0.23/0.55  fof(f1560,plain,(
% 0.23/0.55    ~spl23_25 | spl23_32 | spl23_34),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f1559])).
% 0.23/0.55  fof(f1559,plain,(
% 0.23/0.55    $false | (~spl23_25 | spl23_32 | spl23_34)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1556,f1437])).
% 0.23/0.55  fof(f1556,plain,(
% 0.23/0.55    sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) | (~spl23_25 | spl23_34)),
% 0.23/0.55    inference(resolution,[],[f1553,f262])).
% 0.23/0.55  fof(f1553,plain,(
% 0.23/0.55    sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15) | (~spl23_25 | spl23_34)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1545,f1099])).
% 0.23/0.55  fof(f1545,plain,(
% 0.23/0.55    sP4(a_2_1_lattice3(sK14,sK16),sK14,sK15) | ~r2_hidden(sK15,a_2_1_lattice3(sK14,sK16)) | spl23_34),
% 0.23/0.55    inference(resolution,[],[f1544,f765])).
% 0.23/0.55  fof(f1544,plain,(
% 0.23/0.55    r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16)) | spl23_34),
% 0.23/0.55    inference(subsumption_resolution,[],[f1543,f157])).
% 0.23/0.55  fof(f1543,plain,(
% 0.23/0.55    r4_lattice3(sK14,sK15,a_2_1_lattice3(sK14,sK16)) | ~sP7(sK14,sK15) | spl23_34),
% 0.23/0.55    inference(resolution,[],[f1541,f119])).
% 0.23/0.55  fof(f1541,plain,(
% 0.23/0.55    sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16)) | spl23_34),
% 0.23/0.55    inference(subsumption_resolution,[],[f1540,f88])).
% 0.23/0.55  fof(f1540,plain,(
% 0.23/0.55    sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16)) | v2_struct_0(sK14) | spl23_34),
% 0.23/0.55    inference(subsumption_resolution,[],[f1539,f91])).
% 0.23/0.55  fof(f1539,plain,(
% 0.23/0.55    sP6(sK15,sK14,a_2_1_lattice3(sK14,sK16)) | ~l3_lattices(sK14) | v2_struct_0(sK14) | spl23_34),
% 0.23/0.55    inference(resolution,[],[f1533,f654])).
% 0.23/0.55  fof(f654,plain,(
% 0.23/0.55    ( ! [X2,X0,X3,X1] : (sP12(X0,X1,sK19(X2,X3,a_2_1_lattice3(X1,X0))) | sP6(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.23/0.55    inference(resolution,[],[f217,f145])).
% 0.23/0.55  fof(f145,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f45])).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.23/0.55    inference(definition_folding,[],[f25,f44,f43])).
% 0.23/0.55  fof(f44,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP12(X2,X1,X0)) | ~sP13(X0,X1,X2))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.23/0.55    inference(flattening,[],[f24])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 0.23/0.55    inference(ennf_transformation,[],[f4])).
% 0.23/0.55  fof(f4,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 0.23/0.55  fof(f217,plain,(
% 0.23/0.55    ( ! [X2,X0,X3,X1] : (~sP13(sK19(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP12(X0,X1,sK19(X2,X3,a_2_1_lattice3(X1,X0))) | sP6(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 0.23/0.55    inference(resolution,[],[f139,f122])).
% 0.23/0.55  fof(f122,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK19(X0,X1,X2),X2) | sP6(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f72])).
% 0.23/0.55  fof(f139,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f83])).
% 0.23/0.55  fof(f83,plain,(
% 0.23/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP12(X2,X1,X0)) & (sP12(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP13(X0,X1,X2))),
% 0.23/0.55    inference(nnf_transformation,[],[f44])).
% 0.23/0.55  fof(f1533,plain,(
% 0.23/0.55    ~sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | spl23_34),
% 0.23/0.55    inference(avatar_component_clause,[],[f1531])).
% 0.23/0.55  fof(f1538,plain,(
% 0.23/0.55    ~spl23_34 | spl23_35 | ~spl23_33),
% 0.23/0.55    inference(avatar_split_clause,[],[f1505,f1440,f1535,f1531])).
% 0.23/0.55  fof(f1505,plain,(
% 0.23/0.55    sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~spl23_33),
% 0.23/0.55    inference(subsumption_resolution,[],[f1504,f88])).
% 0.23/0.55  fof(f1504,plain,(
% 0.23/0.55    sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | v2_struct_0(sK14) | ~spl23_33),
% 0.23/0.55    inference(subsumption_resolution,[],[f1489,f91])).
% 0.23/0.55  fof(f1489,plain,(
% 0.23/0.55    sP9(sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~sP12(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | ~l3_lattices(sK14) | v2_struct_0(sK14) | ~spl23_33),
% 0.23/0.55    inference(superposition,[],[f185,f1442])).
% 0.23/0.55  fof(f185,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (sP9(X1,sK22(X0,X1,X2)) | ~sP12(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.23/0.55    inference(resolution,[],[f141,f131])).
% 0.23/0.55  fof(f131,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP9(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (sP9(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(definition_folding,[],[f21,f38,f37])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(flattening,[],[f20])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 0.23/0.55  fof(f141,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) | ~sP12(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f87])).
% 0.23/0.55  fof(f1468,plain,(
% 0.23/0.55    spl23_4 | ~spl23_32),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f1467])).
% 0.23/0.55  fof(f1467,plain,(
% 0.23/0.55    $false | (spl23_4 | ~spl23_32)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1466,f88])).
% 0.23/0.55  fof(f1466,plain,(
% 0.23/0.55    v2_struct_0(sK14) | (spl23_4 | ~spl23_32)),
% 0.23/0.55    inference(subsumption_resolution,[],[f1465,f313])).
% 0.23/0.55  fof(f313,plain,(
% 0.23/0.55    ~sP1(sK16,sK14,sK15) | spl23_4),
% 0.23/0.55    inference(avatar_component_clause,[],[f312])).
% 0.23/0.55  fof(f312,plain,(
% 0.23/0.55    spl23_4 <=> sP1(sK16,sK14,sK15)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl23_4])])).
% 0.23/0.55  fof(f1465,plain,(
% 0.23/0.55    sP1(sK16,sK14,sK15) | v2_struct_0(sK14) | ~spl23_32),
% 0.23/0.55    inference(subsumption_resolution,[],[f1464,f91])).
% 0.23/0.55  fof(f1464,plain,(
% 0.23/0.55    ~l3_lattices(sK14) | sP1(sK16,sK14,sK15) | v2_struct_0(sK14) | ~spl23_32),
% 0.23/0.55    inference(subsumption_resolution,[],[f1463,f90])).
% 0.23/0.55  fof(f1463,plain,(
% 0.23/0.55    ~v4_lattice3(sK14) | ~l3_lattices(sK14) | sP1(sK16,sK14,sK15) | v2_struct_0(sK14) | ~spl23_32),
% 0.23/0.55    inference(subsumption_resolution,[],[f1462,f89])).
% 0.23/0.55  fof(f1462,plain,(
% 0.23/0.55    ~v10_lattices(sK14) | ~v4_lattice3(sK14) | ~l3_lattices(sK14) | sP1(sK16,sK14,sK15) | v2_struct_0(sK14) | ~spl23_32),
% 0.23/0.55    inference(subsumption_resolution,[],[f1447,f94])).
% 0.23/0.55  fof(f94,plain,(
% 0.23/0.55    r3_lattice3(sK14,sK15,sK16)),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f1447,plain,(
% 0.23/0.55    ~r3_lattice3(sK14,sK15,sK16) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | ~l3_lattices(sK14) | sP1(sK16,sK14,sK15) | v2_struct_0(sK14) | ~spl23_32),
% 0.23/0.55    inference(superposition,[],[f1422,f1438])).
% 0.23/0.55  fof(f1438,plain,(
% 0.23/0.55    sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) | ~spl23_32),
% 0.23/0.55    inference(avatar_component_clause,[],[f1436])).
% 0.23/0.55  fof(f1422,plain,(
% 0.23/0.55    ( ! [X4,X3] : (~r3_lattice3(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X4) | ~v10_lattices(X3) | ~v4_lattice3(X3) | ~l3_lattices(X3) | sP1(X4,X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4))) | v2_struct_0(X3)) )),
% 0.23/0.55    inference(resolution,[],[f1420,f102])).
% 0.23/0.55  fof(f102,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~sP0(X2,X1,X0) | sP1(X0,X1,X2) | ~r3_lattice3(X1,X2,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f54])).
% 0.23/0.55  fof(f54,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 0.23/0.55    inference(rectify,[],[f53])).
% 0.23/0.55  fof(f53,plain,(
% 0.23/0.55    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 0.23/0.55    inference(flattening,[],[f52])).
% 0.23/0.55  fof(f52,plain,(
% 0.23/0.55    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | (~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 0.23/0.55    inference(nnf_transformation,[],[f27])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> (sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.23/0.55  fof(f1420,plain,(
% 0.23/0.55    ( ! [X0,X1] : (sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0)) )),
% 0.23/0.55    inference(duplicate_literal_removal,[],[f1419])).
% 0.23/0.55  fof(f1419,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)) )),
% 0.23/0.55    inference(resolution,[],[f1102,f203])).
% 0.23/0.55  fof(f203,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (sP12(X0,X1,sK17(X2,X1,X0)) | sP0(X2,X1,X0)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f199,f104])).
% 0.23/0.55  fof(f104,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f58])).
% 0.23/0.55  fof(f58,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r3_lattices(X1,sK17(X0,X1,X2),X0) & r3_lattice3(X1,sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f56,f57])).
% 0.23/0.55  fof(f57,plain,(
% 0.23/0.55    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK17(X0,X1,X2),X0) & r3_lattice3(X1,sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f56,plain,(
% 0.23/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.23/0.55    inference(rectify,[],[f55])).
% 0.23/0.55  fof(f55,plain,(
% 0.23/0.55    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 0.23/0.55    inference(nnf_transformation,[],[f26])).
% 0.23/0.55  fof(f26,plain,(
% 0.23/0.55    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.23/0.55  fof(f199,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (sP12(X0,X1,sK17(X2,X1,X0)) | ~m1_subset_1(sK17(X2,X1,X0),u1_struct_0(X1)) | sP0(X2,X1,X0)) )),
% 0.23/0.55    inference(resolution,[],[f149,f105])).
% 0.23/0.55  fof(f105,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK17(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f58])).
% 0.23/0.55  fof(f149,plain,(
% 0.23/0.55    ( ! [X0,X3,X1] : (~r3_lattice3(X1,X3,X0) | sP12(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.23/0.55    inference(equality_resolution,[],[f144])).
% 0.23/0.55  fof(f144,plain,(
% 0.23/0.55    ( ! [X2,X0,X3,X1] : (sP12(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f87])).
% 0.23/0.55  fof(f1102,plain,(
% 0.23/0.55    ( ! [X2,X0,X3,X1] : (~sP12(X2,X1,sK17(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.23/0.55    inference(resolution,[],[f416,f145])).
% 0.23/0.55  fof(f416,plain,(
% 0.23/0.55    ( ! [X6,X4,X7,X5] : (~sP13(sK17(k15_lattice3(X4,a_2_1_lattice3(X5,X6)),X4,X7),X5,X6) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | sP0(k15_lattice3(X4,a_2_1_lattice3(X5,X6)),X4,X7) | ~sP12(X6,X5,sK17(k15_lattice3(X4,a_2_1_lattice3(X5,X6)),X4,X7)) | ~l3_lattices(X4)) )),
% 0.23/0.55    inference(resolution,[],[f283,f140])).
% 0.23/0.55  fof(f140,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f83])).
% 0.23/0.55  fof(f283,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK17(k15_lattice3(X0,X1),X0,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f282,f104])).
% 0.23/0.55  fof(f282,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK17(k15_lattice3(X0,X1),X0,X2),X1) | ~m1_subset_1(sK17(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 0.23/0.55    inference(resolution,[],[f96,f106])).
% 0.23/0.55  fof(f106,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK17(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f58])).
% 0.23/0.55  fof(f96,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(flattening,[],[f12])).
% 0.23/0.55  fof(f12,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 0.23/0.55  fof(f1443,plain,(
% 0.23/0.55    spl23_32 | spl23_33 | ~spl23_25),
% 0.23/0.55    inference(avatar_split_clause,[],[f1433,f1098,f1440,f1436])).
% 0.23/0.55  fof(f1433,plain,(
% 0.23/0.55    sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) | ~spl23_25),
% 0.23/0.55    inference(subsumption_resolution,[],[f1432,f88])).
% 0.23/0.55  fof(f1432,plain,(
% 0.23/0.55    v2_struct_0(sK14) | sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) | ~spl23_25),
% 0.23/0.55    inference(subsumption_resolution,[],[f1430,f91])).
% 0.23/0.55  fof(f1430,plain,(
% 0.23/0.55    ~l3_lattices(sK14) | v2_struct_0(sK14) | sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16)) = sK22(sK16,sK14,sK19(sK15,sK14,a_2_1_lattice3(sK14,sK16))) | sK15 = k15_lattice3(sK14,a_2_1_lattice3(sK14,sK16)) | ~spl23_25),
% 0.23/0.55    inference(resolution,[],[f1273,f1099])).
% 0.23/0.55  fof(f1273,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r2_hidden(sK15,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | sK19(sK15,sK14,a_2_1_lattice3(X0,X1)) = sK22(X1,X0,sK19(sK15,sK14,a_2_1_lattice3(X0,X1))) | sK15 = k15_lattice3(sK14,a_2_1_lattice3(X0,X1))) )),
% 0.23/0.55    inference(resolution,[],[f995,f262])).
% 0.23/0.55  fof(f995,plain,(
% 0.23/0.55    ( ! [X54,X55] : (sP4(a_2_1_lattice3(X54,X55),sK14,sK15) | sK19(sK15,sK14,a_2_1_lattice3(X54,X55)) = sK22(X55,X54,sK19(sK15,sK14,a_2_1_lattice3(X54,X55))) | ~l3_lattices(X54) | v2_struct_0(X54) | ~r2_hidden(sK15,a_2_1_lattice3(X54,X55))) )),
% 0.23/0.55    inference(subsumption_resolution,[],[f982,f157])).
% 0.23/0.55  fof(f982,plain,(
% 0.23/0.55    ( ! [X54,X55] : (v2_struct_0(X54) | sK19(sK15,sK14,a_2_1_lattice3(X54,X55)) = sK22(X55,X54,sK19(sK15,sK14,a_2_1_lattice3(X54,X55))) | ~l3_lattices(X54) | ~sP7(sK14,sK15) | sP4(a_2_1_lattice3(X54,X55),sK14,sK15) | ~r2_hidden(sK15,a_2_1_lattice3(X54,X55))) )),
% 0.23/0.55    inference(resolution,[],[f841,f765])).
% 0.23/0.55  fof(f841,plain,(
% 0.23/0.55    ( ! [X6,X8,X7,X5] : (r4_lattice3(X7,X6,a_2_1_lattice3(X5,X8)) | v2_struct_0(X5) | sK19(X6,X7,a_2_1_lattice3(X5,X8)) = sK22(X8,X5,sK19(X6,X7,a_2_1_lattice3(X5,X8))) | ~l3_lattices(X5) | ~sP7(X7,X6)) )),
% 0.23/0.55    inference(resolution,[],[f727,f119])).
% 0.23/0.55  fof(f727,plain,(
% 0.23/0.55    ( ! [X10,X8,X11,X9] : (sP6(X8,X9,a_2_1_lattice3(X10,X11)) | ~l3_lattices(X10) | v2_struct_0(X10) | sK19(X8,X9,a_2_1_lattice3(X10,X11)) = sK22(X11,X10,sK19(X8,X9,a_2_1_lattice3(X10,X11)))) )),
% 0.23/0.55    inference(resolution,[],[f654,f142])).
% 0.23/0.55  fof(f142,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~sP12(X0,X1,X2) | sK22(X0,X1,X2) = X2) )),
% 0.23/0.55    inference(cnf_transformation,[],[f87])).
% 0.23/0.55  fof(f1113,plain,(
% 0.23/0.55    spl23_25),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f1112])).
% 0.23/0.55  fof(f1112,plain,(
% 0.23/0.55    $false | spl23_25),
% 0.23/0.55    inference(subsumption_resolution,[],[f1111,f88])).
% 0.23/0.55  fof(f1111,plain,(
% 0.23/0.55    v2_struct_0(sK14) | spl23_25),
% 0.23/0.55    inference(subsumption_resolution,[],[f1110,f91])).
% 0.23/0.55  fof(f1110,plain,(
% 0.23/0.55    ~l3_lattices(sK14) | v2_struct_0(sK14) | spl23_25),
% 0.23/0.55    inference(resolution,[],[f1109,f145])).
% 0.23/0.55  fof(f1109,plain,(
% 0.23/0.55    ~sP13(sK15,sK14,sK16) | spl23_25),
% 0.23/0.55    inference(subsumption_resolution,[],[f1108,f202])).
% 0.23/0.55  fof(f202,plain,(
% 0.23/0.55    sP12(sK16,sK14,sK15)),
% 0.23/0.55    inference(subsumption_resolution,[],[f198,f92])).
% 0.23/0.55  fof(f198,plain,(
% 0.23/0.55    sP12(sK16,sK14,sK15) | ~m1_subset_1(sK15,u1_struct_0(sK14))),
% 0.23/0.55    inference(resolution,[],[f149,f94])).
% 0.23/0.55  fof(f1108,plain,(
% 0.23/0.55    ~sP12(sK16,sK14,sK15) | ~sP13(sK15,sK14,sK16) | spl23_25),
% 0.23/0.55    inference(resolution,[],[f1100,f140])).
% 0.23/0.55  fof(f1100,plain,(
% 0.23/0.55    ~r2_hidden(sK15,a_2_1_lattice3(sK14,sK16)) | spl23_25),
% 0.23/0.55    inference(avatar_component_clause,[],[f1098])).
% 0.23/0.55  fof(f321,plain,(
% 0.23/0.55    ~spl23_4),
% 0.23/0.55    inference(avatar_contradiction_clause,[],[f320])).
% 0.23/0.55  fof(f320,plain,(
% 0.23/0.55    $false | ~spl23_4),
% 0.23/0.55    inference(subsumption_resolution,[],[f319,f233])).
% 0.23/0.55  fof(f233,plain,(
% 0.23/0.55    sP2(sK15,sK14)),
% 0.23/0.55    inference(subsumption_resolution,[],[f232,f88])).
% 0.23/0.55  fof(f232,plain,(
% 0.23/0.55    sP2(sK15,sK14) | v2_struct_0(sK14)),
% 0.23/0.55    inference(subsumption_resolution,[],[f231,f89])).
% 0.23/0.55  fof(f231,plain,(
% 0.23/0.55    sP2(sK15,sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)),
% 0.23/0.55    inference(subsumption_resolution,[],[f230,f90])).
% 0.23/0.55  fof(f230,plain,(
% 0.23/0.55    sP2(sK15,sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)),
% 0.23/0.55    inference(subsumption_resolution,[],[f223,f91])).
% 0.23/0.55  fof(f223,plain,(
% 0.23/0.55    sP2(sK15,sK14) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)),
% 0.23/0.55    inference(resolution,[],[f107,f92])).
% 0.23/0.55  fof(f107,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f29])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(definition_folding,[],[f15,f28,f27,f26])).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0))),
% 0.23/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.23/0.55  fof(f15,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.23/0.55    inference(flattening,[],[f14])).
% 0.23/0.55  fof(f14,plain,(
% 0.23/0.55    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 0.23/0.55  fof(f319,plain,(
% 0.23/0.55    ~sP2(sK15,sK14) | ~spl23_4),
% 0.23/0.55    inference(subsumption_resolution,[],[f316,f95])).
% 0.23/0.55  fof(f95,plain,(
% 0.23/0.55    sK15 != k16_lattice3(sK14,sK16)),
% 0.23/0.55    inference(cnf_transformation,[],[f49])).
% 0.23/0.55  fof(f316,plain,(
% 0.23/0.55    sK15 = k16_lattice3(sK14,sK16) | ~sP2(sK15,sK14) | ~spl23_4),
% 0.23/0.55    inference(resolution,[],[f314,f99])).
% 0.23/0.55  fof(f99,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (~sP1(X2,X1,X0) | k16_lattice3(X1,X2) = X0 | ~sP2(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f51])).
% 0.23/0.55  fof(f51,plain,(
% 0.23/0.55    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP2(X0,X1))),
% 0.23/0.55    inference(rectify,[],[f50])).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP2(X1,X0))),
% 0.23/0.55    inference(nnf_transformation,[],[f28])).
% 0.23/0.55  fof(f314,plain,(
% 0.23/0.55    sP1(sK16,sK14,sK15) | ~spl23_4),
% 0.23/0.55    inference(avatar_component_clause,[],[f312])).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (28530)------------------------------
% 0.23/0.55  % (28530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (28530)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (28530)Memory used [KB]: 12281
% 0.23/0.55  % (28530)Time elapsed: 0.122 s
% 0.23/0.55  % (28530)------------------------------
% 0.23/0.55  % (28530)------------------------------
% 0.23/0.56  % (28504)Success in time 0.179 s
%------------------------------------------------------------------------------
