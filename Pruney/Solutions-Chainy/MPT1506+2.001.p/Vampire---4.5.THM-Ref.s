%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:41 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 565 expanded)
%              Number of leaves         :   34 ( 189 expanded)
%              Depth                    :   28
%              Number of atoms          : 1158 (3253 expanded)
%              Number of equality atoms :   24 (  76 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1606,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1564,f1590,f1597,f1605])).

fof(f1605,plain,
    ( ~ spl23_8
    | spl23_10 ),
    inference(avatar_contradiction_clause,[],[f1604])).

fof(f1604,plain,
    ( $false
    | ~ spl23_8
    | spl23_10 ),
    inference(subsumption_resolution,[],[f1603,f85])).

fof(f85,plain,(
    ~ v2_struct_0(sK13) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ~ r3_lattices(sK13,sK14,k16_lattice3(sK13,sK15))
    & r3_lattice3(sK13,sK14,sK15)
    & m1_subset_1(sK14,u1_struct_0(sK13))
    & l3_lattices(sK13)
    & v4_lattice3(sK13)
    & v10_lattices(sK13)
    & ~ v2_struct_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f11,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
                & r3_lattice3(X0,X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK13,X1,k16_lattice3(sK13,X2))
              & r3_lattice3(sK13,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK13)) )
      & l3_lattices(sK13)
      & v4_lattice3(sK13)
      & v10_lattices(sK13)
      & ~ v2_struct_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_lattices(sK13,X1,k16_lattice3(sK13,X2))
            & r3_lattice3(sK13,X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK13)) )
   => ( ? [X2] :
          ( ~ r3_lattices(sK13,sK14,k16_lattice3(sK13,X2))
          & r3_lattice3(sK13,sK14,X2) )
      & m1_subset_1(sK14,u1_struct_0(sK13)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK13,sK14,k16_lattice3(sK13,X2))
        & r3_lattice3(sK13,sK14,X2) )
   => ( ~ r3_lattices(sK13,sK14,k16_lattice3(sK13,sK15))
      & r3_lattice3(sK13,sK14,sK15) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
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
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
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
                ( r3_lattice3(X0,X1,X2)
               => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
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
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(f1603,plain,
    ( v2_struct_0(sK13)
    | ~ spl23_8
    | spl23_10 ),
    inference(subsumption_resolution,[],[f1602,f88])).

fof(f88,plain,(
    l3_lattices(sK13) ),
    inference(cnf_transformation,[],[f48])).

fof(f1602,plain,
    ( ~ l3_lattices(sK13)
    | v2_struct_0(sK13)
    | ~ spl23_8
    | spl23_10 ),
    inference(subsumption_resolution,[],[f1601,f768])).

fof(f768,plain,
    ( sP5(sK13)
    | ~ spl23_8 ),
    inference(avatar_component_clause,[],[f767])).

fof(f767,plain,
    ( spl23_8
  <=> sP5(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_8])])).

fof(f1601,plain,
    ( ~ sP5(sK13)
    | ~ l3_lattices(sK13)
    | v2_struct_0(sK13)
    | spl23_10 ),
    inference(subsumption_resolution,[],[f1600,f86])).

fof(f86,plain,(
    v10_lattices(sK13) ),
    inference(cnf_transformation,[],[f48])).

fof(f1600,plain,
    ( ~ v10_lattices(sK13)
    | ~ sP5(sK13)
    | ~ l3_lattices(sK13)
    | v2_struct_0(sK13)
    | spl23_10 ),
    inference(resolution,[],[f1563,f753])).

fof(f753,plain,(
    ! [X4,X3] :
      ( r3_lattice3(X3,sK18(X3,a_2_9_lattice3(X3,X4)),X4)
      | ~ v10_lattices(X3)
      | ~ sP5(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f752,f171])).

fof(f171,plain,(
    ! [X4,X3] :
      ( sP10(X3,sK18(X3,X4))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ sP5(X3) ) ),
    inference(resolution,[],[f134,f112])).

fof(f112,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK18(X0,X3),u1_struct_0(X0))
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( sP5(X0)
        | ! [X2] :
            ( ~ sP4(X2,X0,sK17(X0))
            | ~ r4_lattice3(X0,X2,sK17(X0))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( sP4(sK18(X0,X3),X0,X3)
            & r4_lattice3(X0,sK18(X0,X3),X3)
            & m1_subset_1(sK18(X0,X3),u1_struct_0(X0)) )
        | ~ sP5(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ~ sP4(X2,X0,X1)
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ~ sP4(X2,X0,sK17(X0))
          | ~ r4_lattice3(X0,X2,sK17(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( sP4(X4,X0,X3)
          & r4_lattice3(X0,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP4(sK18(X0,X3),X0,X3)
        & r4_lattice3(X0,sK18(X0,X3),X3)
        & m1_subset_1(sK18(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( sP5(X0)
        | ? [X1] :
          ! [X2] :
            ( ~ sP4(X2,X0,X1)
            | ~ r4_lattice3(X0,X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X3] :
          ? [X4] :
            ( sP4(X4,X0,X3)
            & r4_lattice3(X0,X4,X3)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP5(X0) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( sP5(X0)
        | ? [X1] :
          ! [X2] :
            ( ~ sP4(X2,X0,X1)
            | ~ r4_lattice3(X0,X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X1] :
          ? [X2] :
            ( sP4(X2,X0,X1)
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP5(X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP5(X0)
    <=> ! [X1] :
        ? [X2] :
          ( sP4(X2,X0,X1)
          & r4_lattice3(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP10(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP10(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f40,f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( sP9(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP9(X1,X0,X2) )
      | ~ sP10(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f752,plain,(
    ! [X4,X3] :
      ( v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ sP5(X3)
      | ~ l3_lattices(X3)
      | r3_lattice3(X3,sK18(X3,a_2_9_lattice3(X3,X4)),X4)
      | ~ sP10(X3,sK18(X3,a_2_9_lattice3(X3,X4))) ) ),
    inference(resolution,[],[f750,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP10(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP9(X1,X0,X2) )
          & ( sP9(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP10(X0,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f750,plain,(
    ! [X0,X1] :
      ( sP9(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ sP5(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f748])).

fof(f748,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ sP5(X0)
      | sP9(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | sP9(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f745,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK21(X0,X1,X2),X2)
      | sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK21(X0,X1,X2))
          & r2_hidden(sK21(X0,X1,X2),X2)
          & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f76,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK21(X0,X1,X2))
        & r2_hidden(sK21(X0,X1,X2),X2)
        & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X1,X0,X2] :
      ( ( sP9(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP9(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f745,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),X4)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ sP5(X3)
      | sP9(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5) ) ),
    inference(subsumption_resolution,[],[f744,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))
      | sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f744,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(X3)
      | ~ m1_subset_1(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ r2_hidden(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),X4)
      | ~ v10_lattices(X3)
      | ~ sP5(X3)
      | sP9(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5) ) ),
    inference(subsumption_resolution,[],[f738,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ sP5(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v4_lattice3(X0) ) ),
    inference(resolution,[],[f120,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ sP6(X0)
      | ~ sP5(X0)
      | v4_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ~ sP5(X0) )
        & ( sP5(X0)
          | ~ v4_lattice3(X0) ) )
      | ~ sP6(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> sP5(X0) )
      | ~ sP6(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f120,plain,(
    ! [X0] :
      ( sP6(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( sP6(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f34,f33,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).

fof(f738,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(X3)
      | ~ v4_lattice3(X3)
      | ~ m1_subset_1(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ r2_hidden(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),X4)
      | ~ v10_lattices(X3)
      | ~ sP5(X3)
      | sP9(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5) ) ),
    inference(resolution,[],[f736,f232])).

fof(f232,plain,(
    ! [X4,X5,X3] :
      ( ~ r4_lattice3(X3,sK21(sK18(X3,X4),X3,X5),X4)
      | ~ sP5(X3)
      | sP9(sK18(X3,X4),X3,X5) ) ),
    inference(subsumption_resolution,[],[f230,f131])).

fof(f230,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK21(sK18(X3,X4),X3,X5),u1_struct_0(X3))
      | ~ r4_lattice3(X3,sK21(sK18(X3,X4),X3,X5),X4)
      | ~ sP5(X3)
      | sP9(sK18(X3,X4),X3,X5) ) ),
    inference(resolution,[],[f228,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK21(X0,X1,X2))
      | sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,sK18(X0,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP5(X0) ) ),
    inference(resolution,[],[f116,f114])).

fof(f114,plain,(
    ! [X0,X3] :
      ( sP4(sK18(X0,X3),X0,X3)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f116,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r4_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK19(X0,X1,X2))
          & r4_lattice3(X1,sK19(X0,X1,X2),X2)
          & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK19(X0,X1,X2))
        & r4_lattice3(X1,sK19(X0,X1,X2),X2)
        & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ( sP4(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP4(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f736,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X4,X5,a_2_9_lattice3(X4,X6))
      | v2_struct_0(X4)
      | ~ v4_lattice3(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X5,X6)
      | ~ v10_lattices(X4) ) ),
    inference(subsumption_resolution,[],[f735,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP8(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP8(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f37,f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( sP7(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP7(X1,X0,X2) )
      | ~ sP8(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f735,plain,(
    ! [X6,X4,X5] :
      ( ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ v4_lattice3(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X5,X6)
      | r4_lattice3(X4,X5,a_2_9_lattice3(X4,X6))
      | ~ sP8(X4,X5) ) ),
    inference(resolution,[],[f727,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP7(X1,X0,X2) )
          & ( sP7(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP8(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f727,plain,(
    ! [X2,X0,X1] :
      ( sP7(X1,X0,a_2_9_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f722])).

fof(f722,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP7(X1,X0,a_2_9_lattice3(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X1,X2)
      | sP7(X1,X0,a_2_9_lattice3(X0,X2)) ) ),
    inference(resolution,[],[f418,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK20(X0,X1,X2),X0)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK20(X0,X1,X2),X0)
          & r2_hidden(sK20(X0,X1,X2),X2)
          & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f71,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK20(X0,X1,X2),X0)
        & r2_hidden(sK20(X0,X1,X2),X2)
        & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X1,X0,X2] :
      ( ( sP7(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP7(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f418,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattices(X0,sK20(X1,X2,a_2_9_lattice3(X0,X3)),X4)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP7(X1,X2,a_2_9_lattice3(X0,X3))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X4,X3) ) ),
    inference(subsumption_resolution,[],[f417,f382])).

fof(f382,plain,(
    ! [X10,X8,X11,X9] :
      ( sP10(X10,sK20(X8,X9,a_2_9_lattice3(X10,X11)))
      | ~ l3_lattices(X10)
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10)
      | sP7(X8,X9,a_2_9_lattice3(X10,X11)) ) ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,(
    ! [X10,X8,X11,X9] :
      ( sP7(X8,X9,a_2_9_lattice3(X10,X11))
      | ~ l3_lattices(X10)
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10)
      | sP10(X10,sK20(X8,X9,a_2_9_lattice3(X10,X11)))
      | ~ l3_lattices(X10)
      | v2_struct_0(X10) ) ),
    inference(resolution,[],[f289,f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ sP11(X0,X1,X2)
      | sP10(X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( sP10(X1,X2)
      | ~ sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP11(X0,X1,X2) ) ),
    inference(superposition,[],[f177,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( sK22(X0,X1,X2) = X2
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( sP11(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK22(X0,X1,X2),X0)
          & sK22(X0,X1,X2) = X2
          & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP11(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f82,f83])).

fof(f83,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK22(X0,X1,X2),X0)
        & sK22(X0,X1,X2) = X2
        & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( sP11(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP11(X0,X1,X2) ) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ( sP11(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP11(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( sP11(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( sP10(X1,sK22(X0,X1,X2))
      | ~ sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f139,f134])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f289,plain,(
    ! [X2,X0,X3,X1] :
      ( sP11(X0,X1,sK20(X2,X3,a_2_9_lattice3(X1,X0)))
      | sP7(X2,X3,a_2_9_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f202,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( sP12(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( sP12(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f43,f42])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> sP11(X2,X1,X0) )
      | ~ sP12(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_9_lattice3)).

fof(f202,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP12(sK20(X2,X3,a_2_9_lattice3(X1,X0)),X1,X0)
      | sP11(X0,X1,sK20(X2,X3,a_2_9_lattice3(X1,X0)))
      | sP7(X2,X3,a_2_9_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f137,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK20(X0,X1,X2),X2)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | sP11(X2,X1,X0)
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
          | ~ sP11(X2,X1,X0) )
        & ( sP11(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_9_lattice3(X1,X2)) ) )
      | ~ sP12(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f417,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP7(X1,X2,a_2_9_lattice3(X0,X3))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattices(X0,sK20(X1,X2,a_2_9_lattice3(X0,X3)),X4)
      | ~ r2_hidden(X4,X3)
      | ~ sP10(X0,sK20(X1,X2,a_2_9_lattice3(X0,X3))) ) ),
    inference(resolution,[],[f380,f225])).

fof(f225,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X3,X0)
      | ~ r2_hidden(X0,X1)
      | ~ sP10(X2,X3) ) ),
    inference(resolution,[],[f130,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( sP9(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP10(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f130,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f380,plain,(
    ! [X14,X12,X15,X13] :
      ( r3_lattice3(X14,sK20(X12,X13,a_2_9_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | ~ v4_lattice3(X14)
      | ~ v10_lattices(X14)
      | v2_struct_0(X14)
      | sP7(X12,X13,a_2_9_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f289,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ sP11(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP11(X0,X1,X2)
      | ~ sP11(X0,X1,X2) ) ),
    inference(superposition,[],[f141,f140])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK22(X0,X1,X2),X0)
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f1563,plain,
    ( ~ r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15)
    | spl23_10 ),
    inference(avatar_component_clause,[],[f1561])).

fof(f1561,plain,
    ( spl23_10
  <=> r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_10])])).

fof(f1597,plain,
    ( ~ spl23_8
    | spl23_9 ),
    inference(avatar_contradiction_clause,[],[f1596])).

fof(f1596,plain,
    ( $false
    | ~ spl23_8
    | spl23_9 ),
    inference(subsumption_resolution,[],[f1595,f768])).

fof(f1595,plain,
    ( ~ sP5(sK13)
    | spl23_9 ),
    inference(subsumption_resolution,[],[f1594,f85])).

fof(f1594,plain,
    ( v2_struct_0(sK13)
    | ~ sP5(sK13)
    | spl23_9 ),
    inference(subsumption_resolution,[],[f1593,f86])).

fof(f1593,plain,
    ( ~ v10_lattices(sK13)
    | v2_struct_0(sK13)
    | ~ sP5(sK13)
    | spl23_9 ),
    inference(subsumption_resolution,[],[f1592,f88])).

fof(f1592,plain,
    ( ~ l3_lattices(sK13)
    | ~ v10_lattices(sK13)
    | v2_struct_0(sK13)
    | ~ sP5(sK13)
    | spl23_9 ),
    inference(resolution,[],[f778,f217])).

fof(f217,plain,(
    ! [X4,X3] :
      ( sP3(sK18(X3,X4),X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ sP5(X3) ) ),
    inference(subsumption_resolution,[],[f208,f146])).

fof(f208,plain,(
    ! [X4,X3] :
      ( sP3(sK18(X3,X4),X3)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ sP5(X3) ) ),
    inference(resolution,[],[f109,f112])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP3(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( sP1(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f778,plain,
    ( ~ sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13)
    | spl23_9 ),
    inference(avatar_component_clause,[],[f776])).

fof(f776,plain,
    ( spl23_9
  <=> sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_9])])).

fof(f1590,plain,(
    spl23_8 ),
    inference(avatar_contradiction_clause,[],[f1589])).

fof(f1589,plain,
    ( $false
    | spl23_8 ),
    inference(subsumption_resolution,[],[f1588,f88])).

fof(f1588,plain,
    ( ~ l3_lattices(sK13)
    | spl23_8 ),
    inference(subsumption_resolution,[],[f1587,f87])).

fof(f87,plain,(
    v4_lattice3(sK13) ),
    inference(cnf_transformation,[],[f48])).

fof(f1587,plain,
    ( ~ v4_lattice3(sK13)
    | ~ l3_lattices(sK13)
    | spl23_8 ),
    inference(subsumption_resolution,[],[f1586,f85])).

fof(f1586,plain,
    ( v2_struct_0(sK13)
    | ~ v4_lattice3(sK13)
    | ~ l3_lattices(sK13)
    | spl23_8 ),
    inference(resolution,[],[f769,f147])).

fof(f147,plain,(
    ! [X1] :
      ( sP5(X1)
      | v2_struct_0(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f120,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ sP6(X0)
      | ~ v4_lattice3(X0)
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f769,plain,
    ( ~ sP5(sK13)
    | spl23_8 ),
    inference(avatar_component_clause,[],[f767])).

fof(f1564,plain,
    ( ~ spl23_10
    | ~ spl23_9
    | ~ spl23_8 ),
    inference(avatar_split_clause,[],[f1559,f767,f776,f1561])).

fof(f1559,plain,
    ( ~ sP5(sK13)
    | ~ sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13)
    | ~ r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15) ),
    inference(subsumption_resolution,[],[f1558,f86])).

fof(f1558,plain,
    ( ~ sP5(sK13)
    | ~ v10_lattices(sK13)
    | ~ sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13)
    | ~ r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15) ),
    inference(subsumption_resolution,[],[f1557,f88])).

fof(f1557,plain,
    ( ~ l3_lattices(sK13)
    | ~ sP5(sK13)
    | ~ v10_lattices(sK13)
    | ~ sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13)
    | ~ r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15) ),
    inference(subsumption_resolution,[],[f1544,f85])).

fof(f1544,plain,
    ( v2_struct_0(sK13)
    | ~ l3_lattices(sK13)
    | ~ sP5(sK13)
    | ~ v10_lattices(sK13)
    | ~ sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13)
    | ~ r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15) ),
    inference(resolution,[],[f1543,f332])).

fof(f332,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK13,sK15)
      | ~ sP3(X0,sK13)
      | ~ r3_lattice3(sK13,X0,sK15) ) ),
    inference(resolution,[],[f330,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ sP1(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP1(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f330,plain,(
    ! [X0] :
      ( ~ sP2(sK15,sK13,X0)
      | ~ sP3(X0,sK13) ) ),
    inference(duplicate_literal_removal,[],[f329])).

fof(f329,plain,(
    ! [X0] :
      ( ~ sP3(X0,sK13)
      | ~ sP2(sK15,sK13,X0)
      | ~ sP3(X0,sK13) ) ),
    inference(superposition,[],[f326,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP2(X2,X1,X0) )
          & ( sP2(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP2(X2,X0,X1) )
          & ( sP2(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f326,plain,(
    ~ sP3(k16_lattice3(sK13,sK15),sK13) ),
    inference(subsumption_resolution,[],[f325,f90])).

fof(f90,plain,(
    r3_lattice3(sK13,sK14,sK15) ),
    inference(cnf_transformation,[],[f48])).

fof(f325,plain,
    ( ~ r3_lattice3(sK13,sK14,sK15)
    | ~ sP3(k16_lattice3(sK13,sK15),sK13) ),
    inference(subsumption_resolution,[],[f321,f89])).

fof(f89,plain,(
    m1_subset_1(sK14,u1_struct_0(sK13)) ),
    inference(cnf_transformation,[],[f48])).

fof(f321,plain,
    ( ~ m1_subset_1(sK14,u1_struct_0(sK13))
    | ~ r3_lattice3(sK13,sK14,sK15)
    | ~ sP3(k16_lattice3(sK13,sK15),sK13) ),
    inference(resolution,[],[f226,f91])).

fof(f91,plain,(
    ~ r3_lattices(sK13,sK14,k16_lattice3(sK13,sK15)) ),
    inference(cnf_transformation,[],[f48])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP3(k16_lattice3(X0,X2),X0) ) ),
    inference(resolution,[],[f105,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( sP1(k16_lattice3(X0,X1),X0,X1)
      | ~ sP3(k16_lattice3(X0,X1),X0) ) ),
    inference(resolution,[],[f144,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | sP1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f144,plain,(
    ! [X2,X1] :
      ( sP2(X2,X1,k16_lattice3(X1,X2))
      | ~ sP3(k16_lattice3(X1,X2),X1) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | k16_lattice3(X1,X2) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r3_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r3_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK16(X0,X1,X2),X0)
          & r3_lattice3(X1,sK16(X0,X1,X2),X2)
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK16(X0,X1,X2),X0)
        & r3_lattice3(X1,sK16(X0,X1,X2),X2)
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f1543,plain,(
    ! [X0,X1] :
      ( sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f1542,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1542,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1541,f154])).

fof(f154,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f99,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f99,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f13,f26])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f1541,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ v10_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1540,f151])).

fof(f151,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f99,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1540,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ v10_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1539,f153])).

fof(f153,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f99,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1539,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ v10_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1538,f146])).

fof(f1538,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f1537])).

fof(f1537,plain,(
    ! [X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v9_lattices(X0)
      | ~ m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))
      | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f1390,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK16(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1390,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3),X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ v9_lattices(X0)
      | ~ m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f1376,f145])).

fof(f145,plain,(
    ! [X0,X3,X1] :
      ( sP11(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( sP11(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f1376,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP11(X2,X1,sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3))
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3)
      | ~ l3_lattices(X0)
      | ~ sP5(X0)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f549,f143])).

fof(f549,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP12(sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3),X1,X2)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3)
      | ~ sP11(X2,X1,sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3))
      | ~ sP5(X0) ) ),
    inference(resolution,[],[f499,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_9_lattice3(X1,X2))
      | ~ sP11(X2,X1,X0)
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f499,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK16(sK18(X0,X1),X0,X2),X1)
      | ~ sP5(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f496,f106])).

fof(f496,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK16(sK18(X0,X1),X0,X2),X1)
      | ~ sP5(X0)
      | ~ m1_subset_1(sK16(sK18(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(sK18(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f343,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK16(X0,X1,X2),X0)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f343,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,X0,sK18(X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ sP5(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f342,f112])).

fof(f342,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP5(X1)
      | r3_lattices(X1,X0,sK18(X1,X2))
      | ~ m1_subset_1(sK18(X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f341,f127])).

fof(f341,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP8(X1,sK18(X1,X2))
      | ~ sP5(X1)
      | r3_lattices(X1,X0,sK18(X1,X2))
      | ~ m1_subset_1(sK18(X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP8(X1,sK18(X1,X2))
      | ~ sP5(X1)
      | r3_lattices(X1,X0,sK18(X1,X2))
      | ~ m1_subset_1(sK18(X1,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f252,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X1,X0,sK18(X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP8(X1,sK18(X1,X2))
      | ~ sP5(X1) ) ),
    inference(resolution,[],[f218,f113])).

fof(f113,plain,(
    ! [X0,X3] :
      ( r4_lattice3(X0,sK18(X0,X3),X3)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f218,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X0,X3)
      | ~ r2_hidden(X0,X1)
      | ~ sP8(X2,X3) ) ),
    inference(resolution,[],[f123,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sP7(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f123,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (24930)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (24938)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.47  % (24930)Refutation not found, incomplete strategy% (24930)------------------------------
% 0.21/0.47  % (24930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (24930)Memory used [KB]: 1663
% 0.21/0.47  % (24930)Time elapsed: 0.065 s
% 0.21/0.47  % (24930)------------------------------
% 0.21/0.47  % (24930)------------------------------
% 0.21/0.49  % (24935)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (24927)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (24926)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (24948)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (24928)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (24947)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (24925)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (24923)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (24945)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (24932)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (24923)Refutation not found, incomplete strategy% (24923)------------------------------
% 0.21/0.51  % (24923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24923)Memory used [KB]: 10618
% 0.21/0.51  % (24923)Time elapsed: 0.104 s
% 0.21/0.51  % (24923)------------------------------
% 0.21/0.51  % (24923)------------------------------
% 0.21/0.52  % (24942)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (24933)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (24937)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (24931)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (24940)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (24929)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (24924)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (24941)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (24929)Refutation not found, incomplete strategy% (24929)------------------------------
% 0.21/0.53  % (24929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24929)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24929)Memory used [KB]: 10618
% 0.21/0.53  % (24929)Time elapsed: 0.098 s
% 0.21/0.53  % (24929)------------------------------
% 0.21/0.53  % (24929)------------------------------
% 0.21/0.53  % (24939)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (24946)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (24944)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (24943)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (24934)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (24936)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24936)Refutation not found, incomplete strategy% (24936)------------------------------
% 0.21/0.54  % (24936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24936)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24936)Memory used [KB]: 6140
% 0.21/0.54  % (24936)Time elapsed: 0.139 s
% 0.21/0.54  % (24936)------------------------------
% 0.21/0.54  % (24936)------------------------------
% 2.20/0.64  % (24932)Refutation not found, incomplete strategy% (24932)------------------------------
% 2.20/0.64  % (24932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.64  % (24932)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.64  
% 2.20/0.64  % (24932)Memory used [KB]: 6140
% 2.20/0.64  % (24932)Time elapsed: 0.219 s
% 2.20/0.64  % (24932)------------------------------
% 2.20/0.64  % (24932)------------------------------
% 2.20/0.69  % (24927)Refutation found. Thanks to Tanya!
% 2.20/0.69  % SZS status Theorem for theBenchmark
% 2.20/0.69  % SZS output start Proof for theBenchmark
% 2.20/0.69  fof(f1606,plain,(
% 2.20/0.69    $false),
% 2.20/0.69    inference(avatar_sat_refutation,[],[f1564,f1590,f1597,f1605])).
% 2.20/0.69  fof(f1605,plain,(
% 2.20/0.69    ~spl23_8 | spl23_10),
% 2.20/0.69    inference(avatar_contradiction_clause,[],[f1604])).
% 2.20/0.69  fof(f1604,plain,(
% 2.20/0.69    $false | (~spl23_8 | spl23_10)),
% 2.20/0.69    inference(subsumption_resolution,[],[f1603,f85])).
% 2.20/0.69  fof(f85,plain,(
% 2.20/0.69    ~v2_struct_0(sK13)),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f48,plain,(
% 2.20/0.69    ((~r3_lattices(sK13,sK14,k16_lattice3(sK13,sK15)) & r3_lattice3(sK13,sK14,sK15)) & m1_subset_1(sK14,u1_struct_0(sK13))) & l3_lattices(sK13) & v4_lattice3(sK13) & v10_lattices(sK13) & ~v2_struct_0(sK13)),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f11,f47,f46,f45])).
% 2.20/0.69  fof(f45,plain,(
% 2.20/0.69    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK13,X1,k16_lattice3(sK13,X2)) & r3_lattice3(sK13,X1,X2)) & m1_subset_1(X1,u1_struct_0(sK13))) & l3_lattices(sK13) & v4_lattice3(sK13) & v10_lattices(sK13) & ~v2_struct_0(sK13))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f46,plain,(
% 2.20/0.69    ? [X1] : (? [X2] : (~r3_lattices(sK13,X1,k16_lattice3(sK13,X2)) & r3_lattice3(sK13,X1,X2)) & m1_subset_1(X1,u1_struct_0(sK13))) => (? [X2] : (~r3_lattices(sK13,sK14,k16_lattice3(sK13,X2)) & r3_lattice3(sK13,sK14,X2)) & m1_subset_1(sK14,u1_struct_0(sK13)))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f47,plain,(
% 2.20/0.69    ? [X2] : (~r3_lattices(sK13,sK14,k16_lattice3(sK13,X2)) & r3_lattice3(sK13,sK14,X2)) => (~r3_lattices(sK13,sK14,k16_lattice3(sK13,sK15)) & r3_lattice3(sK13,sK14,sK15))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f11,plain,(
% 2.20/0.69    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.20/0.69    inference(flattening,[],[f10])).
% 2.20/0.69  fof(f10,plain,(
% 2.20/0.69    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,X1,k16_lattice3(X0,X2)) & r3_lattice3(X0,X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f9])).
% 2.20/0.69  fof(f9,negated_conjecture,(
% 2.20/0.69    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 2.20/0.69    inference(negated_conjecture,[],[f8])).
% 2.20/0.69  fof(f8,conjecture,(
% 2.20/0.69    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).
% 2.20/0.69  fof(f1603,plain,(
% 2.20/0.69    v2_struct_0(sK13) | (~spl23_8 | spl23_10)),
% 2.20/0.69    inference(subsumption_resolution,[],[f1602,f88])).
% 2.20/0.69  fof(f88,plain,(
% 2.20/0.69    l3_lattices(sK13)),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f1602,plain,(
% 2.20/0.69    ~l3_lattices(sK13) | v2_struct_0(sK13) | (~spl23_8 | spl23_10)),
% 2.20/0.69    inference(subsumption_resolution,[],[f1601,f768])).
% 2.20/0.69  fof(f768,plain,(
% 2.20/0.69    sP5(sK13) | ~spl23_8),
% 2.20/0.69    inference(avatar_component_clause,[],[f767])).
% 2.20/0.69  fof(f767,plain,(
% 2.20/0.69    spl23_8 <=> sP5(sK13)),
% 2.20/0.69    introduced(avatar_definition,[new_symbols(naming,[spl23_8])])).
% 2.20/0.69  fof(f1601,plain,(
% 2.20/0.69    ~sP5(sK13) | ~l3_lattices(sK13) | v2_struct_0(sK13) | spl23_10),
% 2.20/0.69    inference(subsumption_resolution,[],[f1600,f86])).
% 2.20/0.69  fof(f86,plain,(
% 2.20/0.69    v10_lattices(sK13)),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f1600,plain,(
% 2.20/0.69    ~v10_lattices(sK13) | ~sP5(sK13) | ~l3_lattices(sK13) | v2_struct_0(sK13) | spl23_10),
% 2.20/0.69    inference(resolution,[],[f1563,f753])).
% 2.20/0.69  fof(f753,plain,(
% 2.20/0.69    ( ! [X4,X3] : (r3_lattice3(X3,sK18(X3,a_2_9_lattice3(X3,X4)),X4) | ~v10_lattices(X3) | ~sP5(X3) | ~l3_lattices(X3) | v2_struct_0(X3)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f752,f171])).
% 2.20/0.69  fof(f171,plain,(
% 2.20/0.69    ( ! [X4,X3] : (sP10(X3,sK18(X3,X4)) | ~l3_lattices(X3) | v2_struct_0(X3) | ~sP5(X3)) )),
% 2.20/0.69    inference(resolution,[],[f134,f112])).
% 2.20/0.69  fof(f112,plain,(
% 2.20/0.69    ( ! [X0,X3] : (m1_subset_1(sK18(X0,X3),u1_struct_0(X0)) | ~sP5(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f64])).
% 2.20/0.69  fof(f64,plain,(
% 2.20/0.69    ! [X0] : ((sP5(X0) | ! [X2] : (~sP4(X2,X0,sK17(X0)) | ~r4_lattice3(X0,X2,sK17(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : (sP4(sK18(X0,X3),X0,X3) & r4_lattice3(X0,sK18(X0,X3),X3) & m1_subset_1(sK18(X0,X3),u1_struct_0(X0))) | ~sP5(X0)))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f61,f63,f62])).
% 2.20/0.69  fof(f62,plain,(
% 2.20/0.69    ! [X0] : (? [X1] : ! [X2] : (~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (~sP4(X2,X0,sK17(X0)) | ~r4_lattice3(X0,X2,sK17(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f63,plain,(
% 2.20/0.69    ! [X3,X0] : (? [X4] : (sP4(X4,X0,X3) & r4_lattice3(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) => (sP4(sK18(X0,X3),X0,X3) & r4_lattice3(X0,sK18(X0,X3),X3) & m1_subset_1(sK18(X0,X3),u1_struct_0(X0))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f61,plain,(
% 2.20/0.69    ! [X0] : ((sP5(X0) | ? [X1] : ! [X2] : (~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ? [X4] : (sP4(X4,X0,X3) & r4_lattice3(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) | ~sP5(X0)))),
% 2.20/0.69    inference(rectify,[],[f60])).
% 2.20/0.69  fof(f60,plain,(
% 2.20/0.69    ! [X0] : ((sP5(X0) | ? [X1] : ! [X2] : (~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP5(X0)))),
% 2.20/0.69    inference(nnf_transformation,[],[f33])).
% 2.20/0.69  fof(f33,plain,(
% 2.20/0.69    ! [X0] : (sP5(X0) <=> ! [X1] : ? [X2] : (sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.20/0.69  fof(f134,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP10(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f41])).
% 2.20/0.69  fof(f41,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (sP10(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(definition_folding,[],[f21,f40,f39])).
% 2.20/0.69  fof(f39,plain,(
% 2.20/0.69    ! [X1,X0,X2] : (sP9(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 2.20/0.69  fof(f40,plain,(
% 2.20/0.69    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP9(X1,X0,X2)) | ~sP10(X0,X1))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 2.20/0.69  fof(f21,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(flattening,[],[f20])).
% 2.20/0.69  fof(f20,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f3])).
% 2.20/0.69  fof(f3,axiom,(
% 2.20/0.69    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 2.20/0.69  fof(f752,plain,(
% 2.20/0.69    ( ! [X4,X3] : (v2_struct_0(X3) | ~v10_lattices(X3) | ~sP5(X3) | ~l3_lattices(X3) | r3_lattice3(X3,sK18(X3,a_2_9_lattice3(X3,X4)),X4) | ~sP10(X3,sK18(X3,a_2_9_lattice3(X3,X4)))) )),
% 2.20/0.69    inference(resolution,[],[f750,f129])).
% 2.20/0.69  fof(f129,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~sP9(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP10(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f74])).
% 2.20/0.69  fof(f74,plain,(
% 2.20/0.69    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP9(X1,X0,X2)) & (sP9(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP10(X0,X1))),
% 2.20/0.69    inference(nnf_transformation,[],[f40])).
% 2.20/0.69  fof(f750,plain,(
% 2.20/0.69    ( ! [X0,X1] : (sP9(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | v2_struct_0(X0) | ~v10_lattices(X0) | ~sP5(X0) | ~l3_lattices(X0)) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f748])).
% 2.20/0.69  fof(f748,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~sP5(X0) | sP9(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | sP9(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)) )),
% 2.20/0.69    inference(resolution,[],[f745,f132])).
% 2.20/0.69  fof(f132,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK21(X0,X1,X2),X2) | sP9(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f78])).
% 2.20/0.69  fof(f78,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | (~r1_lattices(X1,X0,sK21(X0,X1,X2)) & r2_hidden(sK21(X0,X1,X2),X2) & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f76,f77])).
% 2.20/0.69  fof(f77,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK21(X0,X1,X2)) & r2_hidden(sK21(X0,X1,X2),X2) & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f76,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 2.20/0.69    inference(rectify,[],[f75])).
% 2.20/0.69  fof(f75,plain,(
% 2.20/0.69    ! [X1,X0,X2] : ((sP9(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP9(X1,X0,X2)))),
% 2.20/0.69    inference(nnf_transformation,[],[f39])).
% 2.20/0.69  fof(f745,plain,(
% 2.20/0.69    ( ! [X4,X5,X3] : (~r2_hidden(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),X4) | ~l3_lattices(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | ~sP5(X3) | sP9(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f744,f131])).
% 2.20/0.69  fof(f131,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) | sP9(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f78])).
% 2.20/0.69  fof(f744,plain,(
% 2.20/0.69    ( ! [X4,X5,X3] : (v2_struct_0(X3) | ~m1_subset_1(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),u1_struct_0(X3)) | ~l3_lattices(X3) | ~r2_hidden(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),X4) | ~v10_lattices(X3) | ~sP5(X3) | sP9(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f738,f146])).
% 2.20/0.69  fof(f146,plain,(
% 2.20/0.69    ( ! [X0] : (~sP5(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v4_lattice3(X0)) )),
% 2.20/0.69    inference(resolution,[],[f120,f111])).
% 2.20/0.69  fof(f111,plain,(
% 2.20/0.69    ( ! [X0] : (~sP6(X0) | ~sP5(X0) | v4_lattice3(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f59])).
% 2.20/0.69  fof(f59,plain,(
% 2.20/0.69    ! [X0] : (((v4_lattice3(X0) | ~sP5(X0)) & (sP5(X0) | ~v4_lattice3(X0))) | ~sP6(X0))),
% 2.20/0.69    inference(nnf_transformation,[],[f34])).
% 2.20/0.69  fof(f34,plain,(
% 2.20/0.69    ! [X0] : ((v4_lattice3(X0) <=> sP5(X0)) | ~sP6(X0))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 2.20/0.69  fof(f120,plain,(
% 2.20/0.69    ( ! [X0] : (sP6(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f35])).
% 2.20/0.69  fof(f35,plain,(
% 2.20/0.69    ! [X0] : (sP6(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(definition_folding,[],[f17,f34,f33,f32])).
% 2.20/0.69  fof(f32,plain,(
% 2.20/0.69    ! [X2,X0,X1] : (sP4(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.20/0.69  fof(f17,plain,(
% 2.20/0.69    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(flattening,[],[f16])).
% 2.20/0.69  fof(f16,plain,(
% 2.20/0.69    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f5])).
% 2.20/0.69  fof(f5,axiom,(
% 2.20/0.69    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattice3)).
% 2.20/0.69  fof(f738,plain,(
% 2.20/0.69    ( ! [X4,X5,X3] : (v2_struct_0(X3) | ~v4_lattice3(X3) | ~m1_subset_1(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),u1_struct_0(X3)) | ~l3_lattices(X3) | ~r2_hidden(sK21(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5),X4) | ~v10_lattices(X3) | ~sP5(X3) | sP9(sK18(X3,a_2_9_lattice3(X3,X4)),X3,X5)) )),
% 2.20/0.69    inference(resolution,[],[f736,f232])).
% 2.20/0.69  fof(f232,plain,(
% 2.20/0.69    ( ! [X4,X5,X3] : (~r4_lattice3(X3,sK21(sK18(X3,X4),X3,X5),X4) | ~sP5(X3) | sP9(sK18(X3,X4),X3,X5)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f230,f131])).
% 2.20/0.69  fof(f230,plain,(
% 2.20/0.69    ( ! [X4,X5,X3] : (~m1_subset_1(sK21(sK18(X3,X4),X3,X5),u1_struct_0(X3)) | ~r4_lattice3(X3,sK21(sK18(X3,X4),X3,X5),X4) | ~sP5(X3) | sP9(sK18(X3,X4),X3,X5)) )),
% 2.20/0.69    inference(resolution,[],[f228,f133])).
% 2.20/0.69  fof(f133,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK21(X0,X1,X2)) | sP9(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f78])).
% 2.20/0.69  fof(f228,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r1_lattices(X0,sK18(X0,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~sP5(X0)) )),
% 2.20/0.69    inference(resolution,[],[f116,f114])).
% 2.20/0.69  fof(f114,plain,(
% 2.20/0.69    ( ! [X0,X3] : (sP4(sK18(X0,X3),X0,X3) | ~sP5(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f64])).
% 2.20/0.69  fof(f116,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f68])).
% 2.20/0.69  fof(f68,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r1_lattices(X1,X0,sK19(X0,X1,X2)) & r4_lattice3(X1,sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f66,f67])).
% 2.20/0.69  fof(f67,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK19(X0,X1,X2)) & r4_lattice3(X1,sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f66,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.20/0.69    inference(rectify,[],[f65])).
% 2.20/0.69  fof(f65,plain,(
% 2.20/0.69    ! [X2,X0,X1] : ((sP4(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP4(X2,X0,X1)))),
% 2.20/0.69    inference(nnf_transformation,[],[f32])).
% 2.20/0.69  fof(f736,plain,(
% 2.20/0.69    ( ! [X6,X4,X5] : (r4_lattice3(X4,X5,a_2_9_lattice3(X4,X6)) | v2_struct_0(X4) | ~v4_lattice3(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l3_lattices(X4) | ~r2_hidden(X5,X6) | ~v10_lattices(X4)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f735,f127])).
% 2.20/0.69  fof(f127,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP8(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f38])).
% 2.20/0.69  fof(f38,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (sP8(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(definition_folding,[],[f19,f37,f36])).
% 2.20/0.69  fof(f36,plain,(
% 2.20/0.69    ! [X1,X0,X2] : (sP7(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 2.20/0.69  fof(f37,plain,(
% 2.20/0.69    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP7(X1,X0,X2)) | ~sP8(X0,X1))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 2.20/0.69  fof(f19,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(flattening,[],[f18])).
% 2.20/0.69  fof(f18,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f4])).
% 2.20/0.69  fof(f4,axiom,(
% 2.20/0.69    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 2.20/0.69  fof(f735,plain,(
% 2.20/0.69    ( ! [X6,X4,X5] : (~v10_lattices(X4) | v2_struct_0(X4) | ~v4_lattice3(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l3_lattices(X4) | ~r2_hidden(X5,X6) | r4_lattice3(X4,X5,a_2_9_lattice3(X4,X6)) | ~sP8(X4,X5)) )),
% 2.20/0.69    inference(resolution,[],[f727,f122])).
% 2.20/0.69  fof(f122,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~sP7(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f69])).
% 2.20/0.69  fof(f69,plain,(
% 2.20/0.69    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP7(X1,X0,X2)) & (sP7(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP8(X0,X1))),
% 2.20/0.69    inference(nnf_transformation,[],[f37])).
% 2.20/0.69  fof(f727,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP7(X1,X0,a_2_9_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~r2_hidden(X1,X2)) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f722])).
% 2.20/0.69  fof(f722,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP7(X1,X0,a_2_9_lattice3(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~r2_hidden(X1,X2) | sP7(X1,X0,a_2_9_lattice3(X0,X2))) )),
% 2.20/0.69    inference(resolution,[],[f418,f126])).
% 2.20/0.69  fof(f126,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK20(X0,X1,X2),X0) | sP7(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f73])).
% 2.20/0.69  fof(f73,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | (~r1_lattices(X1,sK20(X0,X1,X2),X0) & r2_hidden(sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f71,f72])).
% 2.20/0.69  fof(f72,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK20(X0,X1,X2),X0) & r2_hidden(sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f71,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 2.20/0.69    inference(rectify,[],[f70])).
% 2.20/0.69  fof(f70,plain,(
% 2.20/0.69    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP7(X1,X0,X2)))),
% 2.20/0.69    inference(nnf_transformation,[],[f36])).
% 2.20/0.69  fof(f418,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X3,X1] : (r1_lattices(X0,sK20(X1,X2,a_2_9_lattice3(X0,X3)),X4) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP7(X1,X2,a_2_9_lattice3(X0,X3)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~l3_lattices(X0) | ~r2_hidden(X4,X3)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f417,f382])).
% 2.20/0.69  fof(f382,plain,(
% 2.20/0.69    ( ! [X10,X8,X11,X9] : (sP10(X10,sK20(X8,X9,a_2_9_lattice3(X10,X11))) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10) | sP7(X8,X9,a_2_9_lattice3(X10,X11))) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f379])).
% 2.20/0.69  fof(f379,plain,(
% 2.20/0.69    ( ! [X10,X8,X11,X9] : (sP7(X8,X9,a_2_9_lattice3(X10,X11)) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10) | sP10(X10,sK20(X8,X9,a_2_9_lattice3(X10,X11))) | ~l3_lattices(X10) | v2_struct_0(X10)) )),
% 2.20/0.69    inference(resolution,[],[f289,f220])).
% 2.20/0.69  fof(f220,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~sP11(X0,X1,X2) | sP10(X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f219])).
% 2.20/0.69  fof(f219,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP10(X1,X2) | ~sP11(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1) | ~sP11(X0,X1,X2)) )),
% 2.20/0.69    inference(superposition,[],[f177,f140])).
% 2.20/0.69  fof(f140,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sK22(X0,X1,X2) = X2 | ~sP11(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f84])).
% 2.20/0.69  fof(f84,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP11(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))) | ~sP11(X0,X1,X2)))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f82,f83])).
% 2.20/0.69  fof(f83,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f82,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP11(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP11(X0,X1,X2)))),
% 2.20/0.69    inference(rectify,[],[f81])).
% 2.20/0.69  fof(f81,plain,(
% 2.20/0.69    ! [X2,X1,X0] : ((sP11(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP11(X2,X1,X0)))),
% 2.20/0.69    inference(nnf_transformation,[],[f42])).
% 2.20/0.69  fof(f42,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (sP11(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).
% 2.20/0.69  fof(f177,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP10(X1,sK22(X0,X1,X2)) | ~sP11(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(resolution,[],[f139,f134])).
% 2.20/0.69  fof(f139,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) | ~sP11(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f84])).
% 2.20/0.69  fof(f289,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (sP11(X0,X1,sK20(X2,X3,a_2_9_lattice3(X1,X0))) | sP7(X2,X3,a_2_9_lattice3(X1,X0)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(resolution,[],[f202,f143])).
% 2.20/0.69  fof(f143,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP12(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f44])).
% 2.20/0.69  fof(f44,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (sP12(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.20/0.69    inference(definition_folding,[],[f25,f43,f42])).
% 2.20/0.69  fof(f43,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> sP11(X2,X1,X0)) | ~sP12(X0,X1,X2))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).
% 2.20/0.69  fof(f25,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.20/0.69    inference(flattening,[],[f24])).
% 2.20/0.69  fof(f24,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 2.20/0.69    inference(ennf_transformation,[],[f6])).
% 2.20/0.69  fof(f6,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_9_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_9_lattice3)).
% 2.20/0.69  fof(f202,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (~sP12(sK20(X2,X3,a_2_9_lattice3(X1,X0)),X1,X0) | sP11(X0,X1,sK20(X2,X3,a_2_9_lattice3(X1,X0))) | sP7(X2,X3,a_2_9_lattice3(X1,X0))) )),
% 2.20/0.69    inference(resolution,[],[f137,f125])).
% 2.20/0.69  fof(f125,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK20(X0,X1,X2),X2) | sP7(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f73])).
% 2.20/0.69  fof(f137,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_9_lattice3(X1,X2)) | sP11(X2,X1,X0) | ~sP12(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f80])).
% 2.20/0.69  fof(f80,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~sP11(X2,X1,X0)) & (sP11(X2,X1,X0) | ~r2_hidden(X0,a_2_9_lattice3(X1,X2)))) | ~sP12(X0,X1,X2))),
% 2.20/0.69    inference(nnf_transformation,[],[f43])).
% 2.20/0.69  fof(f417,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X3,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP7(X1,X2,a_2_9_lattice3(X0,X3)) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattices(X0,sK20(X1,X2,a_2_9_lattice3(X0,X3)),X4) | ~r2_hidden(X4,X3) | ~sP10(X0,sK20(X1,X2,a_2_9_lattice3(X0,X3)))) )),
% 2.20/0.69    inference(resolution,[],[f380,f225])).
% 2.20/0.69  fof(f225,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X3,X0) | ~r2_hidden(X0,X1) | ~sP10(X2,X3)) )),
% 2.20/0.69    inference(resolution,[],[f130,f128])).
% 2.20/0.69  fof(f128,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP9(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP10(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f74])).
% 2.20/0.69  fof(f130,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (~sP9(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f78])).
% 2.20/0.69  fof(f380,plain,(
% 2.20/0.69    ( ! [X14,X12,X15,X13] : (r3_lattice3(X14,sK20(X12,X13,a_2_9_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | ~v4_lattice3(X14) | ~v10_lattices(X14) | v2_struct_0(X14) | sP7(X12,X13,a_2_9_lattice3(X14,X15))) )),
% 2.20/0.69    inference(resolution,[],[f289,f182])).
% 2.20/0.69  fof(f182,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~sP11(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f181])).
% 2.20/0.69  fof(f181,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP11(X0,X1,X2) | ~sP11(X0,X1,X2)) )),
% 2.20/0.69    inference(superposition,[],[f141,f140])).
% 2.20/0.69  fof(f141,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK22(X0,X1,X2),X0) | ~sP11(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f84])).
% 2.20/0.69  fof(f1563,plain,(
% 2.20/0.69    ~r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15) | spl23_10),
% 2.20/0.69    inference(avatar_component_clause,[],[f1561])).
% 2.20/0.69  fof(f1561,plain,(
% 2.20/0.69    spl23_10 <=> r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15)),
% 2.20/0.69    introduced(avatar_definition,[new_symbols(naming,[spl23_10])])).
% 2.20/0.69  fof(f1597,plain,(
% 2.20/0.69    ~spl23_8 | spl23_9),
% 2.20/0.69    inference(avatar_contradiction_clause,[],[f1596])).
% 2.20/0.69  fof(f1596,plain,(
% 2.20/0.69    $false | (~spl23_8 | spl23_9)),
% 2.20/0.69    inference(subsumption_resolution,[],[f1595,f768])).
% 2.20/0.69  fof(f1595,plain,(
% 2.20/0.69    ~sP5(sK13) | spl23_9),
% 2.20/0.69    inference(subsumption_resolution,[],[f1594,f85])).
% 2.20/0.69  fof(f1594,plain,(
% 2.20/0.69    v2_struct_0(sK13) | ~sP5(sK13) | spl23_9),
% 2.20/0.69    inference(subsumption_resolution,[],[f1593,f86])).
% 2.20/0.69  fof(f1593,plain,(
% 2.20/0.69    ~v10_lattices(sK13) | v2_struct_0(sK13) | ~sP5(sK13) | spl23_9),
% 2.20/0.69    inference(subsumption_resolution,[],[f1592,f88])).
% 2.20/0.69  fof(f1592,plain,(
% 2.20/0.69    ~l3_lattices(sK13) | ~v10_lattices(sK13) | v2_struct_0(sK13) | ~sP5(sK13) | spl23_9),
% 2.20/0.69    inference(resolution,[],[f778,f217])).
% 2.20/0.69  fof(f217,plain,(
% 2.20/0.69    ( ! [X4,X3] : (sP3(sK18(X3,X4),X3) | ~l3_lattices(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~sP5(X3)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f208,f146])).
% 2.20/0.69  fof(f208,plain,(
% 2.20/0.69    ( ! [X4,X3] : (sP3(sK18(X3,X4),X3) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~sP5(X3)) )),
% 2.20/0.69    inference(resolution,[],[f109,f112])).
% 2.20/0.69  fof(f109,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP3(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f31])).
% 2.20/0.69  fof(f31,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(definition_folding,[],[f15,f30,f29,f28])).
% 2.20/0.69  fof(f28,plain,(
% 2.20/0.69    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.20/0.69  fof(f29,plain,(
% 2.20/0.69    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.20/0.69  fof(f30,plain,(
% 2.20/0.69    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP2(X2,X0,X1)) | ~sP3(X1,X0))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.20/0.69  fof(f15,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(flattening,[],[f14])).
% 2.20/0.69  fof(f14,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f7])).
% 2.20/0.69  fof(f7,axiom,(
% 2.20/0.69    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 2.20/0.69  fof(f778,plain,(
% 2.20/0.69    ~sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13) | spl23_9),
% 2.20/0.69    inference(avatar_component_clause,[],[f776])).
% 2.20/0.69  fof(f776,plain,(
% 2.20/0.69    spl23_9 <=> sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13)),
% 2.20/0.69    introduced(avatar_definition,[new_symbols(naming,[spl23_9])])).
% 2.20/0.69  fof(f1590,plain,(
% 2.20/0.69    spl23_8),
% 2.20/0.69    inference(avatar_contradiction_clause,[],[f1589])).
% 2.20/0.69  fof(f1589,plain,(
% 2.20/0.69    $false | spl23_8),
% 2.20/0.69    inference(subsumption_resolution,[],[f1588,f88])).
% 2.20/0.69  fof(f1588,plain,(
% 2.20/0.69    ~l3_lattices(sK13) | spl23_8),
% 2.20/0.69    inference(subsumption_resolution,[],[f1587,f87])).
% 2.20/0.69  fof(f87,plain,(
% 2.20/0.69    v4_lattice3(sK13)),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f1587,plain,(
% 2.20/0.69    ~v4_lattice3(sK13) | ~l3_lattices(sK13) | spl23_8),
% 2.20/0.69    inference(subsumption_resolution,[],[f1586,f85])).
% 2.20/0.69  fof(f1586,plain,(
% 2.20/0.69    v2_struct_0(sK13) | ~v4_lattice3(sK13) | ~l3_lattices(sK13) | spl23_8),
% 2.20/0.69    inference(resolution,[],[f769,f147])).
% 2.20/0.69  fof(f147,plain,(
% 2.20/0.69    ( ! [X1] : (sP5(X1) | v2_struct_0(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1)) )),
% 2.20/0.69    inference(resolution,[],[f120,f110])).
% 2.20/0.69  fof(f110,plain,(
% 2.20/0.69    ( ! [X0] : (~sP6(X0) | ~v4_lattice3(X0) | sP5(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f59])).
% 2.20/0.69  fof(f769,plain,(
% 2.20/0.69    ~sP5(sK13) | spl23_8),
% 2.20/0.69    inference(avatar_component_clause,[],[f767])).
% 2.20/0.69  fof(f1564,plain,(
% 2.20/0.69    ~spl23_10 | ~spl23_9 | ~spl23_8),
% 2.20/0.69    inference(avatar_split_clause,[],[f1559,f767,f776,f1561])).
% 2.20/0.69  fof(f1559,plain,(
% 2.20/0.69    ~sP5(sK13) | ~sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13) | ~r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15)),
% 2.20/0.69    inference(subsumption_resolution,[],[f1558,f86])).
% 2.20/0.69  fof(f1558,plain,(
% 2.20/0.69    ~sP5(sK13) | ~v10_lattices(sK13) | ~sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13) | ~r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15)),
% 2.20/0.69    inference(subsumption_resolution,[],[f1557,f88])).
% 2.20/0.69  fof(f1557,plain,(
% 2.20/0.69    ~l3_lattices(sK13) | ~sP5(sK13) | ~v10_lattices(sK13) | ~sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13) | ~r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15)),
% 2.20/0.69    inference(subsumption_resolution,[],[f1544,f85])).
% 2.20/0.69  fof(f1544,plain,(
% 2.20/0.69    v2_struct_0(sK13) | ~l3_lattices(sK13) | ~sP5(sK13) | ~v10_lattices(sK13) | ~sP3(sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK13) | ~r3_lattice3(sK13,sK18(sK13,a_2_9_lattice3(sK13,sK15)),sK15)),
% 2.20/0.69    inference(resolution,[],[f1543,f332])).
% 2.20/0.69  fof(f332,plain,(
% 2.20/0.69    ( ! [X0] : (~sP1(X0,sK13,sK15) | ~sP3(X0,sK13) | ~r3_lattice3(sK13,X0,sK15)) )),
% 2.20/0.69    inference(resolution,[],[f330,f104])).
% 2.20/0.69  fof(f104,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f54])).
% 2.20/0.69  fof(f54,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP1(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP2(X0,X1,X2)))),
% 2.20/0.69    inference(rectify,[],[f53])).
% 2.20/0.69  fof(f53,plain,(
% 2.20/0.69    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 2.20/0.69    inference(flattening,[],[f52])).
% 2.20/0.69  fof(f52,plain,(
% 2.20/0.69    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | (~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 2.20/0.69    inference(nnf_transformation,[],[f29])).
% 2.20/0.69  fof(f330,plain,(
% 2.20/0.69    ( ! [X0] : (~sP2(sK15,sK13,X0) | ~sP3(X0,sK13)) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f329])).
% 2.20/0.69  fof(f329,plain,(
% 2.20/0.69    ( ! [X0] : (~sP3(X0,sK13) | ~sP2(sK15,sK13,X0) | ~sP3(X0,sK13)) )),
% 2.20/0.69    inference(superposition,[],[f326,f101])).
% 2.20/0.69  fof(f101,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~sP2(X2,X1,X0) | ~sP3(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f51])).
% 2.20/0.69  fof(f51,plain,(
% 2.20/0.69    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP3(X0,X1))),
% 2.20/0.69    inference(rectify,[],[f50])).
% 2.20/0.69  fof(f50,plain,(
% 2.20/0.69    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP3(X1,X0))),
% 2.20/0.69    inference(nnf_transformation,[],[f30])).
% 2.20/0.69  fof(f326,plain,(
% 2.20/0.69    ~sP3(k16_lattice3(sK13,sK15),sK13)),
% 2.20/0.69    inference(subsumption_resolution,[],[f325,f90])).
% 2.20/0.69  fof(f90,plain,(
% 2.20/0.69    r3_lattice3(sK13,sK14,sK15)),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f325,plain,(
% 2.20/0.69    ~r3_lattice3(sK13,sK14,sK15) | ~sP3(k16_lattice3(sK13,sK15),sK13)),
% 2.20/0.69    inference(subsumption_resolution,[],[f321,f89])).
% 2.20/0.69  fof(f89,plain,(
% 2.20/0.69    m1_subset_1(sK14,u1_struct_0(sK13))),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f321,plain,(
% 2.20/0.69    ~m1_subset_1(sK14,u1_struct_0(sK13)) | ~r3_lattice3(sK13,sK14,sK15) | ~sP3(k16_lattice3(sK13,sK15),sK13)),
% 2.20/0.69    inference(resolution,[],[f226,f91])).
% 2.20/0.69  fof(f91,plain,(
% 2.20/0.69    ~r3_lattices(sK13,sK14,k16_lattice3(sK13,sK15))),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f226,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~sP3(k16_lattice3(X0,X2),X0)) )),
% 2.20/0.69    inference(resolution,[],[f105,f183])).
% 2.20/0.69  fof(f183,plain,(
% 2.20/0.69    ( ! [X0,X1] : (sP1(k16_lattice3(X0,X1),X0,X1) | ~sP3(k16_lattice3(X0,X1),X0)) )),
% 2.20/0.69    inference(resolution,[],[f144,f103])).
% 2.20/0.69  fof(f103,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | sP1(X2,X1,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f54])).
% 2.20/0.69  fof(f144,plain,(
% 2.20/0.69    ( ! [X2,X1] : (sP2(X2,X1,k16_lattice3(X1,X2)) | ~sP3(k16_lattice3(X1,X2),X1)) )),
% 2.20/0.69    inference(equality_resolution,[],[f100])).
% 2.20/0.69  fof(f100,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | k16_lattice3(X1,X2) != X0 | ~sP3(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f51])).
% 2.20/0.69  fof(f105,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r3_lattices(X1,X4,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f58])).
% 2.20/0.69  fof(f58,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~r3_lattices(X1,sK16(X0,X1,X2),X0) & r3_lattice3(X1,sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 2.20/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f56,f57])).
% 2.20/0.69  fof(f57,plain,(
% 2.20/0.69    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK16(X0,X1,X2),X0) & r3_lattice3(X1,sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 2.20/0.69    introduced(choice_axiom,[])).
% 2.20/0.69  fof(f56,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 2.20/0.69    inference(rectify,[],[f55])).
% 2.20/0.69  fof(f55,plain,(
% 2.20/0.69    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP1(X1,X0,X2)))),
% 2.20/0.69    inference(nnf_transformation,[],[f28])).
% 2.20/0.69  fof(f1543,plain,(
% 2.20/0.69    ( ! [X0,X1] : (sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | v2_struct_0(X0) | ~l3_lattices(X0) | ~sP5(X0) | ~v10_lattices(X0)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f1542,f106])).
% 2.20/0.69  fof(f106,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) | sP1(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f58])).
% 2.20/0.69  fof(f1542,plain,(
% 2.20/0.69    ( ! [X0,X1] : (v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~l3_lattices(X0) | ~sP5(X0) | ~v10_lattices(X0) | ~m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f1541,f154])).
% 2.20/0.69  fof(f154,plain,(
% 2.20/0.69    ( ! [X6] : (v9_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | ~v10_lattices(X6)) )),
% 2.20/0.69    inference(resolution,[],[f99,f98])).
% 2.20/0.69  fof(f98,plain,(
% 2.20/0.69    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f49])).
% 2.20/0.69  fof(f49,plain,(
% 2.20/0.69    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 2.20/0.69    inference(nnf_transformation,[],[f26])).
% 2.20/0.69  fof(f26,plain,(
% 2.20/0.69    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 2.20/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.20/0.69  fof(f99,plain,(
% 2.20/0.69    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f27])).
% 2.20/0.69  fof(f27,plain,(
% 2.20/0.69    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.20/0.69    inference(definition_folding,[],[f13,f26])).
% 2.20/0.69  fof(f13,plain,(
% 2.20/0.69    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.20/0.69    inference(flattening,[],[f12])).
% 2.20/0.69  fof(f12,plain,(
% 2.20/0.69    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.20/0.69    inference(ennf_transformation,[],[f1])).
% 2.20/0.69  fof(f1,axiom,(
% 2.20/0.69    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 2.20/0.69  fof(f1541,plain,(
% 2.20/0.69    ( ! [X0,X1] : (v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~l3_lattices(X0) | ~sP5(X0) | ~v10_lattices(X0) | ~v9_lattices(X0) | ~m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f1540,f151])).
% 2.20/0.69  fof(f151,plain,(
% 2.20/0.69    ( ! [X3] : (v6_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v10_lattices(X3)) )),
% 2.20/0.69    inference(resolution,[],[f99,f95])).
% 2.20/0.69  fof(f95,plain,(
% 2.20/0.69    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f49])).
% 2.20/0.69  fof(f1540,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~l3_lattices(X0) | ~sP5(X0) | ~v10_lattices(X0) | ~v9_lattices(X0) | ~m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f1539,f153])).
% 2.20/0.69  fof(f153,plain,(
% 2.20/0.69    ( ! [X5] : (v8_lattices(X5) | v2_struct_0(X5) | ~l3_lattices(X5) | ~v10_lattices(X5)) )),
% 2.20/0.69    inference(resolution,[],[f99,f97])).
% 2.20/0.69  fof(f97,plain,(
% 2.20/0.69    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f49])).
% 2.20/0.69  fof(f1539,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~l3_lattices(X0) | ~sP5(X0) | ~v10_lattices(X0) | ~v9_lattices(X0) | ~m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f1538,f146])).
% 2.20/0.69  fof(f1538,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~l3_lattices(X0) | ~sP5(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~v9_lattices(X0) | ~m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f1537])).
% 2.20/0.69  fof(f1537,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1) | ~l3_lattices(X0) | ~sP5(X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~v9_lattices(X0) | ~m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) | sP1(sK18(X0,a_2_9_lattice3(X0,X1)),X0,X1)) )),
% 2.20/0.69    inference(resolution,[],[f1390,f107])).
% 2.20/0.69  fof(f107,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK16(X0,X1,X2),X2) | sP1(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f58])).
% 2.20/0.69  fof(f1390,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3),X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3) | ~l3_lattices(X0) | ~sP5(X0) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~v9_lattices(X0) | ~m1_subset_1(sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3),u1_struct_0(X1))) )),
% 2.20/0.69    inference(resolution,[],[f1376,f145])).
% 2.20/0.69  fof(f145,plain,(
% 2.20/0.69    ( ! [X0,X3,X1] : (sP11(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.20/0.69    inference(equality_resolution,[],[f142])).
% 2.20/0.69  fof(f142,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (sP11(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f84])).
% 2.20/0.69  fof(f1376,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (~sP11(X2,X1,sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3)) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3) | ~l3_lattices(X0) | ~sP5(X0) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(resolution,[],[f549,f143])).
% 2.20/0.69  fof(f549,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (~sP12(sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3),X1,X2) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3) | ~sP11(X2,X1,sK16(sK18(X0,a_2_9_lattice3(X1,X2)),X0,X3)) | ~sP5(X0)) )),
% 2.20/0.69    inference(resolution,[],[f499,f138])).
% 2.20/0.69  fof(f138,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_9_lattice3(X1,X2)) | ~sP11(X2,X1,X0) | ~sP12(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f80])).
% 2.20/0.69  fof(f499,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r2_hidden(sK16(sK18(X0,X1),X0,X2),X1) | ~sP5(X0) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,X1),X0,X2)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f496,f106])).
% 2.20/0.69  fof(f496,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r2_hidden(sK16(sK18(X0,X1),X0,X2),X1) | ~sP5(X0) | ~m1_subset_1(sK16(sK18(X0,X1),X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(sK18(X0,X1),X0,X2)) )),
% 2.20/0.69    inference(resolution,[],[f343,f108])).
% 2.20/0.69  fof(f108,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK16(X0,X1,X2),X0) | sP1(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f58])).
% 2.20/0.69  fof(f343,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r3_lattices(X1,X0,sK18(X1,X2)) | ~r2_hidden(X0,X2) | ~sP5(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f342,f112])).
% 2.20/0.69  fof(f342,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP5(X1) | r3_lattices(X1,X0,sK18(X1,X2)) | ~m1_subset_1(sK18(X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(subsumption_resolution,[],[f341,f127])).
% 2.20/0.69  fof(f341,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP8(X1,sK18(X1,X2)) | ~sP5(X1) | r3_lattices(X1,X0,sK18(X1,X2)) | ~m1_subset_1(sK18(X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f339])).
% 2.20/0.69  fof(f339,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP8(X1,sK18(X1,X2)) | ~sP5(X1) | r3_lattices(X1,X0,sK18(X1,X2)) | ~m1_subset_1(sK18(X1,X2),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 2.20/0.69    inference(resolution,[],[f252,f136])).
% 2.20/0.69  fof(f136,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f79])).
% 2.20/0.69  fof(f79,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(nnf_transformation,[],[f23])).
% 2.20/0.69  fof(f23,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.20/0.69    inference(flattening,[],[f22])).
% 2.20/0.69  fof(f22,plain,(
% 2.20/0.69    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f2])).
% 2.20/0.69  fof(f2,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 2.20/0.69  fof(f252,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r1_lattices(X1,X0,sK18(X1,X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP8(X1,sK18(X1,X2)) | ~sP5(X1)) )),
% 2.20/0.69    inference(resolution,[],[f218,f113])).
% 2.20/0.69  fof(f113,plain,(
% 2.20/0.69    ( ! [X0,X3] : (r4_lattice3(X0,sK18(X0,X3),X3) | ~sP5(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f64])).
% 2.20/0.69  fof(f218,plain,(
% 2.20/0.69    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X0,X3) | ~r2_hidden(X0,X1) | ~sP8(X2,X3)) )),
% 2.20/0.69    inference(resolution,[],[f123,f121])).
% 2.20/0.69  fof(f121,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (sP7(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f69])).
% 2.20/0.69  fof(f123,plain,(
% 2.20/0.69    ( ! [X4,X2,X0,X1] : (~sP7(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f73])).
% 2.20/0.69  % SZS output end Proof for theBenchmark
% 2.20/0.69  % (24927)------------------------------
% 2.20/0.69  % (24927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.69  % (24927)Termination reason: Refutation
% 2.20/0.69  
% 2.20/0.69  % (24927)Memory used [KB]: 7164
% 2.20/0.69  % (24927)Time elapsed: 0.279 s
% 2.20/0.69  % (24927)------------------------------
% 2.20/0.69  % (24927)------------------------------
% 2.20/0.69  % (24922)Success in time 0.335 s
%------------------------------------------------------------------------------
