%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1539+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 468 expanded)
%              Number of leaves         :   38 ( 153 expanded)
%              Depth                    :   35
%              Number of atoms          : 1050 (2484 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f656,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f230,f234,f239,f655])).

fof(f655,plain,
    ( spl27_2
    | ~ spl27_4 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | spl27_2
    | ~ spl27_4 ),
    inference(subsumption_resolution,[],[f653,f93])).

fof(f93,plain,(
    v5_orders_2(sK15) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ r2_yellow_0(sK15,sK16)
      | ~ r1_yellow_0(sK15,sK16) )
    & l1_orders_2(sK15)
    & v3_lattice3(sK15)
    & v5_orders_2(sK15)
    & ~ v2_struct_0(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f10,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            | ~ r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_yellow_0(sK15,X1)
          | ~ r1_yellow_0(sK15,X1) )
      & l1_orders_2(sK15)
      & v3_lattice3(sK15)
      & v5_orders_2(sK15)
      & ~ v2_struct_0(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ~ r2_yellow_0(sK15,X1)
        | ~ r1_yellow_0(sK15,X1) )
   => ( ~ r2_yellow_0(sK15,sK16)
      | ~ r1_yellow_0(sK15,sK16) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          | ~ r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( r2_yellow_0(X0,X1)
            & r1_yellow_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f653,plain,
    ( ~ v5_orders_2(sK15)
    | spl27_2
    | ~ spl27_4 ),
    inference(subsumption_resolution,[],[f652,f95])).

fof(f95,plain,(
    l1_orders_2(sK15) ),
    inference(cnf_transformation,[],[f46])).

fof(f652,plain,
    ( ~ l1_orders_2(sK15)
    | ~ v5_orders_2(sK15)
    | spl27_2
    | ~ spl27_4 ),
    inference(subsumption_resolution,[],[f651,f228])).

fof(f228,plain,
    ( sP1(sK15)
    | ~ spl27_4 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl27_4
  <=> sP1(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_4])])).

fof(f651,plain,
    ( ~ sP1(sK15)
    | ~ l1_orders_2(sK15)
    | ~ v5_orders_2(sK15)
    | spl27_2 ),
    inference(subsumption_resolution,[],[f650,f92])).

fof(f92,plain,(
    ~ v2_struct_0(sK15) ),
    inference(cnf_transformation,[],[f46])).

fof(f650,plain,
    ( v2_struct_0(sK15)
    | ~ sP1(sK15)
    | ~ l1_orders_2(sK15)
    | ~ v5_orders_2(sK15)
    | spl27_2 ),
    inference(resolution,[],[f648,f159])).

fof(f159,plain,
    ( ~ r2_yellow_0(sK15,sK16)
    | spl27_2 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl27_2
  <=> r2_yellow_0(sK15,sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_2])])).

fof(f648,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | v2_struct_0(X0)
      | ~ sP1(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f647,f132])).

fof(f132,plain,(
    ! [X0] :
      ( sP9(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP9(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f18,f35,f34,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sP7(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X3,X2)
          | ~ r1_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f34,plain,(
    ! [X1,X0] :
      ( sP8(X1,X0)
    <=> ? [X2] :
          ( sP7(X2,X0,X1)
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP8(X1,X0) )
      | ~ sP9(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f647,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP1(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ sP9(X0) ) ),
    inference(resolution,[],[f646,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ sP8(X1,X0)
      | r2_yellow_0(X0,X1)
      | ~ sP9(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP8(X1,X0) )
          & ( sP8(X1,X0)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP9(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f646,plain,(
    ! [X4,X3] :
      ( sP8(X4,X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP1(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f645,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK18(X0,X3),u1_struct_0(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ! [X2] :
            ( ~ sP0(X2,X0,sK17(X0))
            | ~ r2_lattice3(X0,sK17(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( sP0(sK18(X0,X3),X0,X3)
            & r2_lattice3(X0,X3,sK18(X0,X3))
            & m1_subset_1(sK18(X0,X3),u1_struct_0(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ~ sP0(X2,X0,X1)
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ~ sP0(X2,X0,sK17(X0))
          | ~ r2_lattice3(X0,sK17(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( sP0(X4,X0,X3)
          & r2_lattice3(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP0(sK18(X0,X3),X0,X3)
        & r2_lattice3(X0,X3,sK18(X0,X3))
        & m1_subset_1(sK18(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ? [X1] :
          ! [X2] :
            ( ~ sP0(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X3] :
          ? [X4] :
            ( sP0(X4,X0,X3)
            & r2_lattice3(X0,X3,X4)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ? [X1] :
          ! [X2] :
            ( ~ sP0(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X1] :
          ? [X2] :
            ( sP0(X2,X0,X1)
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
        ? [X2] :
          ( sP0(X2,X0,X1)
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f645,plain,(
    ! [X4,X3] :
      ( ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP1(X3)
      | sP8(X4,X3)
      | ~ m1_subset_1(sK18(X3,a_2_0_yellow_0(X3,X4)),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f644,f498])).

fof(f498,plain,(
    ! [X4,X3] :
      ( r1_lattice3(X3,X4,sK18(X3,a_2_0_yellow_0(X3,X4)))
      | ~ l1_orders_2(X3)
      | ~ sP1(X3)
      | v2_struct_0(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f497,f99])).

fof(f497,plain,(
    ! [X4,X3] :
      ( ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3)
      | ~ sP1(X3)
      | v2_struct_0(X3)
      | r1_lattice3(X3,X4,sK18(X3,a_2_0_yellow_0(X3,X4)))
      | ~ m1_subset_1(sK18(X3,a_2_0_yellow_0(X3,X4)),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,(
    ! [X4,X3] :
      ( ~ v5_orders_2(X3)
      | ~ l1_orders_2(X3)
      | ~ sP1(X3)
      | v2_struct_0(X3)
      | r1_lattice3(X3,X4,sK18(X3,a_2_0_yellow_0(X3,X4)))
      | ~ m1_subset_1(sK18(X3,a_2_0_yellow_0(X3,X4)),u1_struct_0(X3))
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f494,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r1_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f109,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP4(X1,X0,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f14,f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( ( r1_lattice3(X0,X1,X2)
      <=> sP3(X2,X0,X1) )
      | ~ sP4(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ sP3(X2,X1,X0)
      | r1_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_lattice3(X1,X0,X2)
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r1_lattice3(X1,X0,X2) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X0,X2] :
      ( ( ( r1_lattice3(X0,X1,X2)
          | ~ sP3(X2,X0,X1) )
        & ( sP3(X2,X0,X1)
          | ~ r1_lattice3(X0,X1,X2) ) )
      | ~ sP4(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f494,plain,(
    ! [X0,X1] :
      ( sP3(sK18(X0,a_2_0_yellow_0(X0,X1)),X0,X1)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ sP1(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f492])).

fof(f492,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ sP1(X0)
      | sP3(sK18(X0,a_2_0_yellow_0(X0,X1)),X0,X1)
      | sP3(sK18(X0,a_2_0_yellow_0(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f482,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK20(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK20(X0,X1,X2))
          & r2_hidden(sK20(X0,X1,X2),X2)
          & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK20(X0,X1,X2))
        & r2_hidden(sK20(X0,X1,X2),X2)
        & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_hidden(X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f482,plain,(
    ! [X14,X15,X13] :
      ( ~ r2_hidden(sK20(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15),X14)
      | v2_struct_0(X13)
      | ~ v5_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ sP1(X13)
      | sP3(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15) ) ),
    inference(subsumption_resolution,[],[f481,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f481,plain,(
    ! [X14,X15,X13] :
      ( ~ v5_orders_2(X13)
      | v2_struct_0(X13)
      | ~ m1_subset_1(sK20(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15),u1_struct_0(X13))
      | ~ r2_hidden(sK20(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15),X14)
      | ~ l1_orders_2(X13)
      | ~ sP1(X13)
      | sP3(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15) ) ),
    inference(subsumption_resolution,[],[f467,f162])).

fof(f162,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f98,f107])).

fof(f107,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f12,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f12,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                 => r1_orders_2(X0,X2,X3) ) )
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

fof(f98,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ sP1(X0)
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v3_lattice3(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f467,plain,(
    ! [X14,X15,X13] :
      ( ~ v5_orders_2(X13)
      | v2_struct_0(X13)
      | ~ m1_subset_1(sK20(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15),u1_struct_0(X13))
      | ~ r2_hidden(sK20(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15),X14)
      | ~ l1_orders_2(X13)
      | ~ v3_lattice3(X13)
      | ~ sP1(X13)
      | sP3(sK18(X13,a_2_0_yellow_0(X13,X14)),X13,X15) ) ),
    inference(resolution,[],[f462,f199])).

fof(f199,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(X3,X4,sK20(sK18(X3,X4),X3,X5))
      | ~ sP1(X3)
      | sP3(sK18(X3,X4),X3,X5) ) ),
    inference(subsumption_resolution,[],[f196,f111])).

fof(f196,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK20(sK18(X3,X4),X3,X5),u1_struct_0(X3))
      | ~ r2_lattice3(X3,X4,sK20(sK18(X3,X4),X3,X5))
      | ~ sP1(X3)
      | sP3(sK18(X3,X4),X3,X5) ) ),
    inference(resolution,[],[f192,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK20(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK18(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f103,f101])).

fof(f101,plain,(
    ! [X0,X3] :
      ( sP0(sK18(X0,X3),X0,X3)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK19(X0,X1,X2))
          & r2_lattice3(X1,X2,sK19(X0,X1,X2))
          & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK19(X0,X1,X2))
        & r2_lattice3(X1,X2,sK19(X0,X1,X2))
        & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f462,plain,(
    ! [X6,X4,X5] :
      ( r2_lattice3(X4,a_2_0_yellow_0(X4,X6),X5)
      | ~ v5_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r2_hidden(X5,X6)
      | ~ l1_orders_2(X4)
      | ~ v3_lattice3(X4) ) ),
    inference(duplicate_literal_removal,[],[f461])).

fof(f461,plain,(
    ! [X6,X4,X5] :
      ( ~ v3_lattice3(X4)
      | ~ v5_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r2_hidden(X5,X6)
      | ~ l1_orders_2(X4)
      | r2_lattice3(X4,a_2_0_yellow_0(X4,X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f456,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | r2_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f116,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sP6(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP6(X1,X0,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f16,f31,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X3,X2)
          | ~ r2_hidden(X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( r2_lattice3(X0,X1,X2)
      <=> sP5(X2,X0,X1) )
      | ~ sP6(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ sP5(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_lattice3(X1,X0,X2)
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | ~ r2_lattice3(X1,X0,X2) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_lattice3(X0,X1,X2)
          | ~ sP5(X2,X0,X1) )
        & ( sP5(X2,X0,X1)
          | ~ r2_lattice3(X0,X1,X2) ) )
      | ~ sP6(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f456,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0,a_2_0_yellow_0(X0,X2))
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f452])).

fof(f452,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,X2)
      | sP5(X1,X0,a_2_0_yellow_0(X0,X2))
      | sP5(X1,X0,a_2_0_yellow_0(X0,X2)) ) ),
    inference(resolution,[],[f337,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK21(X0,X1,X2),X0)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ r1_orders_2(X1,sK21(X0,X1,X2),X0)
          & r2_hidden(sK21(X0,X1,X2),X2)
          & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK21(X0,X1,X2),X0)
        & r2_hidden(sK21(X0,X1,X2),X2)
        & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ( sP5(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r2_hidden(X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP5(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f337,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X2,sK21(X0,X1,a_2_0_yellow_0(X2,X3)),X4)
      | ~ l1_orders_2(X2)
      | ~ v3_lattice3(X2)
      | ~ v5_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r2_hidden(X4,X3)
      | sP5(X0,X1,a_2_0_yellow_0(X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X0,X1,a_2_0_yellow_0(X2,X3))
      | ~ l1_orders_2(X2)
      | ~ v3_lattice3(X2)
      | ~ v5_orders_2(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r2_hidden(X4,X3)
      | ~ l1_orders_2(X2)
      | r1_orders_2(X2,sK21(X0,X1,a_2_0_yellow_0(X2,X3)),X4) ) ),
    inference(resolution,[],[f235,f310])).

fof(f310,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP13(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | ~ l1_orders_2(X1)
      | r1_orders_2(X1,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | ~ l1_orders_2(X1)
      | ~ sP13(X0,X1,X2)
      | ~ sP13(X0,X1,X2) ) ),
    inference(superposition,[],[f260,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( sK26(X0,X1,X2) = X2
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( sP13(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_lattice3(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r1_lattice3(X1,X0,sK26(X0,X1,X2))
          & sK26(X0,X1,X2) = X2
          & m1_subset_1(sK26(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP13(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26])],[f89,f90])).

fof(f90,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r1_lattice3(X1,X0,X4)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r1_lattice3(X1,X0,sK26(X0,X1,X2))
        & sK26(X0,X1,X2) = X2
        & m1_subset_1(sK26(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( sP13(X0,X1,X2)
        | ! [X3] :
            ( ~ r1_lattice3(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r1_lattice3(X1,X0,X4)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP13(X0,X1,X2) ) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ( sP13(X2,X1,X0)
        | ! [X3] :
            ( ~ r1_lattice3(X1,X2,X3)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP13(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f41])).

% (5287)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f41,plain,(
    ! [X2,X1,X0] :
      ( sP13(X2,X1,X0)
    <=> ? [X3] :
          ( r1_lattice3(X1,X2,X3)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).

fof(f260,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_orders_2(X8,sK26(X9,X8,X10),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X8))
      | ~ r2_hidden(X7,X9)
      | ~ l1_orders_2(X8)
      | ~ sP13(X9,X8,X10) ) ),
    inference(subsumption_resolution,[],[f257,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK26(X0,X1,X2),u1_struct_0(X1))
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f257,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(X8))
      | r1_orders_2(X8,sK26(X9,X8,X10),X7)
      | ~ r2_hidden(X7,X9)
      | ~ m1_subset_1(sK26(X9,X8,X10),u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ sP13(X9,X8,X10) ) ),
    inference(resolution,[],[f185,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X0,sK26(X0,X1,X2))
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X2,X1,X3)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_orders_2(X2,X3,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f110,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f108,f114])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X2)
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f235,plain,(
    ! [X2,X0,X3,X1] :
      ( sP13(X0,X1,sK21(X2,X3,a_2_0_yellow_0(X1,X0)))
      | sP5(X2,X3,a_2_0_yellow_0(X1,X0))
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f180,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( sP14(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( sP14(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f22,f42,f41])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> sP13(X2,X1,X0) )
      | ~ sP14(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP14])])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_orders_2(X1)
        & v3_lattice3(X1)
        & v5_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      <=> ? [X3] :
            ( r1_lattice3(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow_0)).

fof(f180,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP14(sK21(X6,X7,a_2_0_yellow_0(X5,X4)),X5,X4)
      | sP13(X4,X5,sK21(X6,X7,a_2_0_yellow_0(X5,X4)))
      | sP5(X6,X7,a_2_0_yellow_0(X5,X4)) ) ),
    inference(resolution,[],[f144,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK21(X0,X1,X2),X2)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | sP13(X2,X1,X0)
      | ~ sP14(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
          | ~ sP13(X2,X1,X0) )
        & ( sP13(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_yellow_0(X1,X2)) ) )
      | ~ sP14(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f644,plain,(
    ! [X4,X3] :
      ( ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | ~ sP1(X3)
      | sP8(X4,X3)
      | ~ r1_lattice3(X3,X4,sK18(X3,a_2_0_yellow_0(X3,X4)))
      | ~ m1_subset_1(sK18(X3,a_2_0_yellow_0(X3,X4)),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f639,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X1,X0)
      | sP8(X0,X1)
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ! [X2] :
            ( ~ sP7(X2,X1,X0)
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ( sP7(sK22(X0,X1),X1,X0)
          & r1_lattice3(X1,X0,sK22(X0,X1))
          & m1_subset_1(sK22(X0,X1),u1_struct_0(X1)) )
        | ~ sP8(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f71,f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( sP7(X3,X1,X0)
          & r1_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sP7(sK22(X0,X1),X1,X0)
        & r1_lattice3(X1,X0,sK22(X0,X1))
        & m1_subset_1(sK22(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ! [X2] :
            ( ~ sP7(X2,X1,X0)
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP7(X3,X1,X0)
            & r1_lattice3(X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP8(X0,X1) ) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ( sP8(X1,X0)
        | ! [X2] :
            ( ~ sP7(X2,X0,X1)
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP7(X2,X0,X1)
            & r1_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP8(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f639,plain,(
    ! [X6,X5] :
      ( sP7(sK18(X5,a_2_0_yellow_0(X5,X6)),X5,X6)
      | ~ l1_orders_2(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5)
      | ~ sP1(X5) ) ),
    inference(subsumption_resolution,[],[f638,f99])).

fof(f638,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(sK18(X5,a_2_0_yellow_0(X5,X6)),u1_struct_0(X5))
      | sP7(sK18(X5,a_2_0_yellow_0(X5,X6)),X5,X6)
      | ~ l1_orders_2(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5)
      | ~ sP1(X5) ) ),
    inference(subsumption_resolution,[],[f632,f162])).

fof(f632,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(sK18(X5,a_2_0_yellow_0(X5,X6)),u1_struct_0(X5))
      | sP7(sK18(X5,a_2_0_yellow_0(X5,X6)),X5,X6)
      | ~ l1_orders_2(X5)
      | ~ v3_lattice3(X5)
      | ~ v5_orders_2(X5)
      | v2_struct_0(X5)
      | ~ sP1(X5) ) ),
    inference(resolution,[],[f629,f100])).

fof(f100,plain,(
    ! [X0,X3] :
      ( r2_lattice3(X0,X3,sK18(X0,X3))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f629,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X1,a_2_0_yellow_0(X1,X2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP7(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f628,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ( ~ r1_orders_2(X1,sK23(X0,X1,X2),X0)
          & r1_lattice3(X1,X2,sK23(X0,X1,X2))
          & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f75,f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK23(X0,X1,X2),X0)
        & r1_lattice3(X1,X2,sK23(X0,X1,X2))
        & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X3,X0)
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ( sP7(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP7(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f628,plain,(
    ! [X2,X0,X1] :
      ( sP7(X0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_lattice3(X1,a_2_0_yellow_0(X1,X2),X0)
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f627])).

fof(f627,plain,(
    ! [X2,X0,X1] :
      ( sP7(X0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_lattice3(X1,a_2_0_yellow_0(X1,X2),X0)
      | ~ l1_orders_2(X1)
      | ~ v3_lattice3(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1))
      | sP7(X0,X1,X2) ) ),
    inference(resolution,[],[f521,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X1,X2,sK23(X0,X1,X2))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f521,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_lattice3(X3,X4,sK23(X1,X0,X2))
      | sP7(X1,X0,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,a_2_0_yellow_0(X3,X4),X1)
      | ~ l1_orders_2(X3)
      | ~ v3_lattice3(X3)
      | ~ v5_orders_2(X3)
      | v2_struct_0(X3)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(sK23(X1,X0,X2),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f421,f151])).

fof(f151,plain,(
    ! [X0,X3,X1] :
      ( sP13(X0,X1,X3)
      | ~ r1_lattice3(X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( sP13(X0,X1,X2)
      | ~ r1_lattice3(X1,X0,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f421,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP13(X3,X4,sK23(X0,X1,X2))
      | ~ l1_orders_2(X1)
      | sP7(X0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_lattice3(X1,a_2_0_yellow_0(X4,X3),X0)
      | ~ l1_orders_2(X4)
      | ~ v3_lattice3(X4)
      | ~ v5_orders_2(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f354,f150])).

fof(f354,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP14(sK23(X3,X0,X4),X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP7(X3,X0,X4)
      | ~ sP13(X2,X1,sK23(X3,X0,X4))
      | ~ r2_lattice3(X0,a_2_0_yellow_0(X1,X2),X3) ) ),
    inference(resolution,[],[f292,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_0_yellow_0(X1,X2))
      | ~ sP13(X2,X1,X0)
      | ~ sP14(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f292,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(sK23(X16,X17,X18),X19)
      | ~ r2_lattice3(X17,X19,X16)
      | ~ m1_subset_1(X16,u1_struct_0(X17))
      | ~ l1_orders_2(X17)
      | sP7(X16,X17,X18) ) ),
    inference(subsumption_resolution,[],[f287,f129])).

fof(f287,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ m1_subset_1(sK23(X16,X17,X18),u1_struct_0(X17))
      | ~ r2_hidden(sK23(X16,X17,X18),X19)
      | ~ r2_lattice3(X17,X19,X16)
      | ~ m1_subset_1(X16,u1_struct_0(X17))
      | ~ l1_orders_2(X17)
      | sP7(X16,X17,X18) ) ),
    inference(resolution,[],[f188,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK23(X0,X1,X2),X0)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X2,X0,X3)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_lattice3(X2,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f117,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f115,f121])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP5(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f239,plain,(
    spl27_4 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl27_4 ),
    inference(subsumption_resolution,[],[f237,f95])).

fof(f237,plain,
    ( ~ l1_orders_2(sK15)
    | spl27_4 ),
    inference(subsumption_resolution,[],[f236,f94])).

fof(f94,plain,(
    v3_lattice3(sK15) ),
    inference(cnf_transformation,[],[f46])).

fof(f236,plain,
    ( ~ v3_lattice3(sK15)
    | ~ l1_orders_2(sK15)
    | spl27_4 ),
    inference(resolution,[],[f229,f161])).

fof(f161,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f97,f107])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v3_lattice3(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f229,plain,
    ( ~ sP1(sK15)
    | spl27_4 ),
    inference(avatar_component_clause,[],[f227])).

fof(f234,plain,(
    spl27_3 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl27_3 ),
    inference(subsumption_resolution,[],[f232,f93])).

fof(f232,plain,
    ( ~ v5_orders_2(sK15)
    | spl27_3 ),
    inference(subsumption_resolution,[],[f231,f95])).

fof(f231,plain,
    ( ~ l1_orders_2(sK15)
    | ~ v5_orders_2(sK15)
    | spl27_3 ),
    inference(resolution,[],[f225,f143])).

fof(f143,plain,(
    ! [X0] :
      ( sP12(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( sP12(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f20,f39,f38,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP10(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sP11(X1,X0)
    <=> ? [X2] :
          ( sP10(X2,X0,X1)
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> sP11(X1,X0) )
      | ~ sP12(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f225,plain,
    ( ~ sP12(sK15)
    | spl27_3 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl27_3
  <=> sP12(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_3])])).

fof(f230,plain,
    ( ~ spl27_3
    | ~ spl27_4
    | spl27_1 ),
    inference(avatar_split_clause,[],[f221,f153,f227,f223])).

fof(f153,plain,
    ( spl27_1
  <=> r1_yellow_0(sK15,sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl27_1])])).

fof(f221,plain,
    ( ~ sP1(sK15)
    | ~ sP12(sK15)
    | spl27_1 ),
    inference(resolution,[],[f220,f155])).

fof(f155,plain,
    ( ~ r1_yellow_0(sK15,sK16)
    | spl27_1 ),
    inference(avatar_component_clause,[],[f153])).

fof(f220,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ sP1(X0)
      | ~ sP12(X0) ) ),
    inference(resolution,[],[f219,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ sP11(X1,X0)
      | r1_yellow_0(X0,X1)
      | ~ sP12(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ~ sP11(X1,X0) )
          & ( sP11(X1,X0)
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ sP12(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f219,plain,(
    ! [X4,X3] :
      ( sP11(X4,X3)
      | ~ sP1(X3) ) ),
    inference(subsumption_resolution,[],[f218,f99])).

fof(f218,plain,(
    ! [X4,X3] :
      ( ~ sP1(X3)
      | sP11(X4,X3)
      | ~ m1_subset_1(sK18(X3,X4),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f217,f100])).

fof(f217,plain,(
    ! [X4,X3] :
      ( ~ sP1(X3)
      | sP11(X4,X3)
      | ~ r2_lattice3(X3,X4,sK18(X3,X4))
      | ~ m1_subset_1(sK18(X3,X4),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f215,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ sP10(X2,X1,X0)
      | sP11(X0,X1)
      | ~ r2_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( sP11(X0,X1)
        | ! [X2] :
            ( ~ sP10(X2,X1,X0)
            | ~ r2_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ( sP10(sK24(X0,X1),X1,X0)
          & r2_lattice3(X1,X0,sK24(X0,X1))
          & m1_subset_1(sK24(X0,X1),u1_struct_0(X1)) )
        | ~ sP11(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f80,f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( sP10(X3,X1,X0)
          & r2_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sP10(sK24(X0,X1),X1,X0)
        & r2_lattice3(X1,X0,sK24(X0,X1))
        & m1_subset_1(sK24(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( sP11(X0,X1)
        | ! [X2] :
            ( ~ sP10(X2,X1,X0)
            | ~ r2_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP10(X3,X1,X0)
            & r2_lattice3(X1,X0,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP11(X0,X1) ) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ( sP11(X1,X0)
        | ! [X2] :
            ( ~ sP10(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP10(X2,X0,X1)
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP11(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f215,plain,(
    ! [X0,X1] :
      ( sP10(sK18(X0,X1),X0,X1)
      | ~ sP1(X0) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0)
      | sP10(sK18(X0,X1),X0,X1)
      | sP10(sK18(X0,X1),X0,X1) ) ),
    inference(resolution,[],[f200,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK25(X0,X1,X2))
      | sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK25(X0,X1,X2))
          & r2_lattice3(X1,X2,sK25(X0,X1,X2))
          & m1_subset_1(sK25(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f84,f85])).

fof(f85,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK25(X0,X1,X2))
        & r2_lattice3(X1,X2,sK25(X0,X1,X2))
        & m1_subset_1(sK25(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(rectify,[],[f83])).

% (5279)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ( sP10(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X2,X3)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP10(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f200,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_lattice3(X6,X7,sK25(sK18(X6,X7),X6,X8))
      | ~ sP1(X6)
      | sP10(sK18(X6,X7),X6,X8) ) ),
    inference(subsumption_resolution,[],[f197,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK25(X0,X1,X2),u1_struct_0(X1))
      | sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f197,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK25(sK18(X6,X7),X6,X8),u1_struct_0(X6))
      | ~ r2_lattice3(X6,X7,sK25(sK18(X6,X7),X6,X8))
      | ~ sP1(X6)
      | sP10(sK18(X6,X7),X6,X8) ) ),
    inference(resolution,[],[f192,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK25(X0,X1,X2))
      | sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f160,plain,
    ( ~ spl27_1
    | ~ spl27_2 ),
    inference(avatar_split_clause,[],[f96,f157,f153])).

fof(f96,plain,
    ( ~ r2_yellow_0(sK15,sK16)
    | ~ r1_yellow_0(sK15,sK16) ),
    inference(cnf_transformation,[],[f46])).

%------------------------------------------------------------------------------
