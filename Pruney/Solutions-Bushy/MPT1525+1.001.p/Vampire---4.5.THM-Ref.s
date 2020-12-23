%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1525+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 368 expanded)
%              Number of leaves         :   21 ( 121 expanded)
%              Depth                    :   27
%              Number of atoms          :  646 (1807 expanded)
%              Number of equality atoms :   65 ( 271 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f83,f247,f308,f311,f315,f319,f334])).

fof(f334,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f332,f36])).

fof(f36,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v3_lattice3(sK4)
    & v3_lattice3(sK3)
    & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    & l1_orders_2(sK4)
    & l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f9,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_lattice3(X1)
            & v3_lattice3(X0)
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(sK3)
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
          & l1_orders_2(X1) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ v3_lattice3(X1)
        & v3_lattice3(sK3)
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        & l1_orders_2(X1) )
   => ( ~ v3_lattice3(sK4)
      & v3_lattice3(sK3)
      & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_lattice3(X1)
          & v3_lattice3(X0)
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( ( v3_lattice3(X0)
                & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
             => v3_lattice3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( ( v3_lattice3(X0)
              & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) )
           => v3_lattice3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_0)).

fof(f332,plain,
    ( ~ l1_orders_2(sK4)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f331,f39])).

fof(f39,plain,(
    ~ v3_lattice3(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f331,plain,
    ( v3_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ spl8_3 ),
    inference(resolution,[],[f99,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f12,f20,f19,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
        ? [X2] :
          ( sP0(X2,X0,X1)
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_lattice3)).

fof(f42,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ sP1(X0)
      | v3_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( ( v3_lattice3(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v3_lattice3(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f99,plain,
    ( sP1(sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_3
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f319,plain,
    ( ~ spl8_7
    | spl8_3
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f318,f298,f240,f78,f74,f98,f294])).

fof(f294,plain,
    ( spl8_7
  <=> r2_lattice3(sK4,sK5(sK4),sK6(sK3,sK5(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f74,plain,
    ( spl8_1
  <=> m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f78,plain,
    ( spl8_2
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_struct_0(sK4) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f240,plain,
    ( spl8_6
  <=> sP1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f298,plain,
    ( spl8_8
  <=> m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f318,plain,
    ( sP1(sK4)
    | ~ r2_lattice3(sK4,sK5(sK4),sK6(sK3,sK5(sK4)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f317,f299])).

fof(f299,plain,
    ( m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK3))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f298])).

fof(f317,plain,
    ( ~ m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK3))
    | sP1(sK4)
    | ~ r2_lattice3(sK4,sK5(sK4),sK6(sK3,sK5(sK4)))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(forward_demodulation,[],[f316,f89])).

fof(f89,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_struct_0(sK4) = X0 )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f316,plain,
    ( sP1(sK4)
    | ~ r2_lattice3(sK4,sK5(sK4),sK6(sK3,sK5(sK4)))
    | ~ m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK4))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f288,f299])).

fof(f288,plain,
    ( ~ m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK3))
    | sP1(sK4)
    | ~ r2_lattice3(sK4,sK5(sK4),sK6(sK3,sK5(sK4)))
    | ~ m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK4))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f287,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ sP0(X2,X0,sK5(X0))
      | sP1(X0)
      | ~ r2_lattice3(X0,sK5(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ! [X2] :
            ( ~ sP0(X2,X0,sK5(X0))
            | ~ r2_lattice3(X0,sK5(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( sP0(sK6(X0,X3),X0,X3)
            & r2_lattice3(X0,X3,sK6(X0,X3))
            & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ~ sP0(X2,X0,X1)
          | ~ r2_lattice3(X0,X1,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ~ sP0(X2,X0,sK5(X0))
          | ~ r2_lattice3(X0,sK5(X0),X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( sP0(X4,X0,X3)
          & r2_lattice3(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP0(sK6(X0,X3),X0,X3)
        & r2_lattice3(X0,X3,sK6(X0,X3))
        & m1_subset_1(sK6(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f287,plain,
    ( ! [X2] :
        ( sP0(sK6(sK3,X2),sK4,X2)
        | ~ m1_subset_1(sK6(sK3,X2),u1_struct_0(sK3)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK6(sK3,X2),u1_struct_0(sK3))
        | sP0(sK6(sK3,X2),sK4,X2)
        | sP0(sK6(sK3,X2),sK4,X2) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f284,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK7(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK7(X0,X1,X2))
          & r2_lattice3(X1,X2,sK7(X0,X1,X2))
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK7(X0,X1,X2))
        & r2_lattice3(X1,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK4,X0,sK7(sK6(sK3,X0),sK4,X1))
        | ~ m1_subset_1(sK6(sK3,X0),u1_struct_0(sK3))
        | sP0(sK6(sK3,X0),sK4,X1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f283,f93])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(X0,sK4,X1),u1_struct_0(sK3))
        | sP0(X0,sK4,X1) )
    | ~ spl8_2 ),
    inference(superposition,[],[f48,f89])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( sP0(sK6(sK3,X0),sK4,X1)
        | ~ m1_subset_1(sK6(sK3,X0),u1_struct_0(sK3))
        | ~ m1_subset_1(sK7(sK6(sK3,X0),sK4,X1),u1_struct_0(sK3))
        | ~ r2_lattice3(sK4,X0,sK7(sK6(sK3,X0),sK4,X1)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f282,f210])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK3,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_lattice3(sK4,X0,X1) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f208,f35])).

fof(f35,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK4,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_lattice3(sK3,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK4,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_lattice3(sK3,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | ~ r2_lattice3(sK4,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_lattice3(X0,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f142,f121])).

fof(f121,plain,
    ( u1_orders_2(sK3) = u1_orders_2(sK4)
    | ~ spl8_1 ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_orders_2(sK4) = X1 )
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f84,f75])).

fof(f75,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f84,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | u1_orders_2(sK4) = X1
      | ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ) ),
    inference(superposition,[],[f57,f37])).

fof(f37,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r2_lattice3(sK4,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_lattice3(X0,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f136,f36])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r2_lattice3(sK4,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_lattice3(X0,X1,X2)
        | ~ l1_orders_2(X0)
        | ~ l1_orders_2(sK4) )
    | ~ spl8_2 ),
    inference(superposition,[],[f63,f89])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X1,X2,X4)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f282,plain,
    ( ! [X2,X3] :
        ( ~ r2_lattice3(sK3,X2,sK7(sK6(sK3,X2),sK4,X3))
        | sP0(sK6(sK3,X2),sK4,X3)
        | ~ m1_subset_1(sK6(sK3,X2),u1_struct_0(sK3)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f281,f93])).

fof(f281,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK6(sK3,X2),u1_struct_0(sK3))
        | sP0(sK6(sK3,X2),sK4,X3)
        | ~ m1_subset_1(sK7(sK6(sK3,X2),sK4,X3),u1_struct_0(sK3))
        | ~ r2_lattice3(sK3,X2,sK7(sK6(sK3,X2),sK4,X3)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f277,f241])).

fof(f241,plain,
    ( sP1(sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f240])).

fof(f277,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK6(sK3,X2),u1_struct_0(sK3))
        | sP0(sK6(sK3,X2),sK4,X3)
        | ~ m1_subset_1(sK7(sK6(sK3,X2),sK4,X3),u1_struct_0(sK3))
        | ~ r2_lattice3(sK3,X2,sK7(sK6(sK3,X2),sK4,X3))
        | ~ sP1(sK3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f275,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ sP1(X0) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( sP0(sK6(X0,X3),X0,X3)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f275,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK3,X2,sK7(X2,sK4,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | sP0(X2,sK4,X3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f273,f93])).

fof(f273,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK7(X2,sK4,X3),u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X2,sK7(X2,sK4,X3))
        | sP0(X2,sK4,X3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f271,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK7(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK4,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X0,X1) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f269,f35])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_orders_2(sK4,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK3,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_orders_2(sK4,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f200])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK4,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f199,f121])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK4,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f189,f36])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK4,X1,X2)
        | ~ l1_orders_2(sK4)
        | ~ l1_orders_2(X0) )
    | ~ spl8_2 ),
    inference(superposition,[],[f61,f89])).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f315,plain,
    ( ~ spl8_6
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl8_6
    | spl8_9 ),
    inference(subsumption_resolution,[],[f313,f241])).

fof(f313,plain,
    ( ~ sP1(sK3)
    | spl8_9 ),
    inference(resolution,[],[f307,f44])).

fof(f44,plain,(
    ! [X0,X3] :
      ( r2_lattice3(X0,X3,sK6(X0,X3))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f307,plain,
    ( ~ r2_lattice3(sK3,sK5(sK4),sK6(sK3,sK5(sK4)))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl8_9
  <=> r2_lattice3(sK3,sK5(sK4),sK6(sK3,sK5(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f311,plain,
    ( ~ spl8_6
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl8_6
    | spl8_8 ),
    inference(subsumption_resolution,[],[f309,f241])).

fof(f309,plain,
    ( ~ sP1(sK3)
    | spl8_8 ),
    inference(resolution,[],[f300,f43])).

fof(f43,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK6(X0,X3),u1_struct_0(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f300,plain,
    ( ~ m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK3))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f298])).

fof(f308,plain,
    ( ~ spl8_9
    | ~ spl8_8
    | ~ spl8_1
    | ~ spl8_2
    | spl8_7 ),
    inference(avatar_split_clause,[],[f303,f294,f78,f74,f298,f305])).

fof(f303,plain,
    ( ~ m1_subset_1(sK6(sK3,sK5(sK4)),u1_struct_0(sK3))
    | ~ r2_lattice3(sK3,sK5(sK4),sK6(sK3,sK5(sK4)))
    | ~ spl8_1
    | ~ spl8_2
    | spl8_7 ),
    inference(resolution,[],[f296,f216])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK4,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_lattice3(sK3,X0,X1) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f214,f35])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK3,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_lattice3(sK4,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK3,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | r2_lattice3(sK4,X0,X1)
        | ~ l1_orders_2(sK3) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | ~ r2_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_lattice3(sK4,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f147,f121])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r2_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_lattice3(sK4,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f138,f36])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
        | ~ r2_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_lattice3(sK4,X1,X2)
        | ~ l1_orders_2(sK4)
        | ~ l1_orders_2(X0) )
    | ~ spl8_2 ),
    inference(superposition,[],[f63,f89])).

fof(f296,plain,
    ( ~ r2_lattice3(sK4,sK5(sK4),sK6(sK3,sK5(sK4)))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f294])).

fof(f247,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl8_6 ),
    inference(subsumption_resolution,[],[f245,f35])).

fof(f245,plain,
    ( ~ l1_orders_2(sK3)
    | spl8_6 ),
    inference(subsumption_resolution,[],[f244,f38])).

fof(f38,plain,(
    v3_lattice3(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f244,plain,
    ( ~ v3_lattice3(sK3)
    | ~ l1_orders_2(sK3)
    | spl8_6 ),
    inference(resolution,[],[f242,f64])).

fof(f64,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f41,f51])).

fof(f41,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v3_lattice3(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f242,plain,
    ( ~ sP1(sK3)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f240])).

fof(f83,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f81,f36])).

fof(f81,plain,
    ( ~ l1_orders_2(sK4)
    | spl8_1 ),
    inference(resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f76,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f80,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f70,f78,f74])).

fof(f70,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | u1_struct_0(sK4) = X0
      | ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ) ),
    inference(superposition,[],[f56,f37])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
