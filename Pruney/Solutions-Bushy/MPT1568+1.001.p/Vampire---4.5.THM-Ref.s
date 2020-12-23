%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1568+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 620 expanded)
%              Number of leaves         :   22 ( 193 expanded)
%              Depth                    :   27
%              Number of atoms          :  714 (3904 expanded)
%              Number of equality atoms :   32 ( 189 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f875,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f99,f322,f329,f394,f574,f579,f598,f858,f874])).

fof(f874,plain,
    ( ~ spl12_4
    | ~ spl12_7
    | ~ spl12_25
    | ~ spl12_30 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_25
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f872,f90])).

fof(f90,plain,
    ( sP3(sK5,sK6)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl12_4
  <=> sP3(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f872,plain,
    ( ~ sP3(sK5,sK6)
    | ~ spl12_7
    | ~ spl12_25
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f871,f316])).

fof(f316,plain,
    ( m1_subset_1(sK8(sK5,sK6),u1_struct_0(sK5))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl12_7
  <=> m1_subset_1(sK8(sK5,sK6),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f871,plain,
    ( ~ m1_subset_1(sK8(sK5,sK6),u1_struct_0(sK5))
    | ~ sP3(sK5,sK6)
    | ~ spl12_25
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f863,f560])).

fof(f560,plain,
    ( r2_lattice3(sK5,sK6,sK8(sK5,sK6))
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl12_25
  <=> r2_lattice3(sK5,sK6,sK8(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f863,plain,
    ( ~ r2_lattice3(sK5,sK6,sK8(sK5,sK6))
    | ~ m1_subset_1(sK8(sK5,sK6),u1_struct_0(sK5))
    | ~ sP3(sK5,sK6)
    | ~ spl12_30 ),
    inference(resolution,[],[f842,f133])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ sP0(sK8(X2,X3),X2,X3)
      | ~ sP3(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ sP3(X2,X3)
      | ~ sP0(sK8(X2,X3),X2,X3)
      | ~ sP0(sK8(X2,X3),X2,X3) ) ),
    inference(resolution,[],[f70,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK11(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( r1_orders_2(X1,X0,X3)
            | ~ r2_lattice3(X1,X2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( ~ r1_orders_2(X1,X0,sK11(X0,X1,X2))
          & r2_lattice3(X1,X2,sK11(X0,X1,X2))
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X0,X4)
          & r2_lattice3(X1,X2,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK11(X0,X1,X2))
        & r2_lattice3(X1,X2,sK11(X0,X1,X2))
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( r1_orders_2(X1,X0,X3)
            | ~ r2_lattice3(X1,X2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( ~ r1_orders_2(X1,X0,X4)
            & r2_lattice3(X1,X2,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X3,X0,X1] :
      ( ( sP0(X3,X0,X1)
        | ! [X4] :
            ( r1_orders_2(X0,X3,X4)
            | ~ r2_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
      & ( ? [X4] :
            ( ~ r1_orders_2(X0,X3,X4)
            & r2_lattice3(X0,X1,X4)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X3,X0,X1] :
      ( sP0(X3,X0,X1)
    <=> ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_lattice3(X3,X4,sK11(sK8(X3,X4),X3,X5))
      | ~ sP3(X3,X4)
      | ~ sP0(sK8(X3,X4),X3,X5) ) ),
    inference(subsumption_resolution,[],[f68,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK11(sK8(X3,X4),X3,X5),u1_struct_0(X3))
      | ~ r2_lattice3(X3,X4,sK11(sK8(X3,X4),X3,X5))
      | ~ sP3(X3,X4)
      | ~ sP0(sK8(X3,X4),X3,X5) ) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK11(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK8(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ sP3(X0,X1) ) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP1(sK8(X0,X1),X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ! [X2] :
            ( ~ sP2(X2,X1,X0)
            | ~ sP1(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ( sP2(sK8(X0,X1),X1,X0)
          & sP1(sK8(X0,X1),X0,X1)
          & r2_lattice3(X0,X1,sK8(X0,X1))
          & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( sP2(X3,X1,X0)
          & sP1(X3,X0,X1)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sP2(sK8(X0,X1),X1,X0)
        & sP1(sK8(X0,X1),X0,X1)
        & r2_lattice3(X0,X1,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ! [X2] :
            ( ~ sP2(X2,X1,X0)
            | ~ sP1(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X3] :
            ( sP2(X3,X1,X0)
            & sP1(X3,X0,X1)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ! [X2] :
            ( ~ sP2(X2,X1,X0)
            | ~ sP1(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP2(X2,X1,X0)
            & sP1(X2,X0,X1)
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ? [X2] :
          ( sP2(X2,X1,X0)
          & sP1(X2,X0,X1)
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK10(X0,X1,X2))
          & r2_lattice3(X1,X2,sK10(X0,X1,X2))
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK10(X0,X1,X2))
        & r2_lattice3(X1,X2,sK10(X0,X1,X2))
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ? [X5] :
            ( ~ r1_orders_2(X0,X2,X5)
            & r2_lattice3(X0,X1,X5)
            & m1_subset_1(X5,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( r1_orders_2(X0,X2,X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ! [X5] :
          ( r1_orders_2(X0,X2,X5)
          | ~ r2_lattice3(X0,X1,X5)
          | ~ m1_subset_1(X5,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f842,plain,
    ( ! [X4] :
        ( sP0(X4,sK5,sK6)
        | ~ r2_lattice3(sK5,sK6,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK5)) )
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f841])).

fof(f841,plain,
    ( spl12_30
  <=> ! [X4] :
        ( sP0(X4,sK5,sK6)
        | ~ r2_lattice3(sK5,sK6,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f858,plain,
    ( spl12_5
    | spl12_30
    | ~ spl12_4
    | ~ spl12_27 ),
    inference(avatar_split_clause,[],[f857,f577,f89,f841,f296])).

fof(f296,plain,
    ( spl12_5
  <=> ! [X0] : sP2(X0,sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f577,plain,
    ( spl12_27
  <=> ! [X3,X4] :
        ( X3 != X4
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK7,X3)
        | ~ sP1(X3,sK5,sK7)
        | sP0(X4,sK5,sK6)
        | ~ m1_subset_1(X4,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK6,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f857,plain,
    ( ! [X12,X11] :
        ( sP0(X12,sK5,sK6)
        | ~ m1_subset_1(X12,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK6,X12)
        | sP2(X11,sK7,sK5) )
    | ~ spl12_4
    | ~ spl12_27 ),
    inference(subsumption_resolution,[],[f856,f262])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( sK9(X0,sK7,sK5) = X1
        | ~ r2_lattice3(sK5,sK6,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | sP0(X1,sK5,sK6)
        | sP2(X0,sK7,sK5) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f261,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( sK9(X0,X1,X2) != X0
          & ~ sP0(sK9(X0,X1,X2),X2,X1)
          & r2_lattice3(X2,X1,sK9(X0,X1,X2))
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( X0 = X4
            | sP0(X4,X2,X1)
            | ~ r2_lattice3(X2,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ~ sP0(X3,X2,X1)
          & r2_lattice3(X2,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( sK9(X0,X1,X2) != X0
        & ~ sP0(sK9(X0,X1,X2),X2,X1)
        & r2_lattice3(X2,X1,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ~ sP0(X3,X2,X1)
            & r2_lattice3(X2,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( X0 = X4
            | sP0(X4,X2,X1)
            | ~ r2_lattice3(X2,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ( sP2(X2,X1,X0)
        | ? [X3] :
            ( X2 != X3
            & ~ sP0(X3,X0,X1)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | sP0(X3,X0,X1)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( sP2(X2,X1,X0)
    <=> ! [X3] :
          ( X2 = X3
          | sP0(X3,X0,X1)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( sK9(X0,sK7,sK5) = X1
        | ~ r2_lattice3(sK5,sK6,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | sP0(X1,sK5,sK6)
        | sP2(X0,sK7,sK5)
        | ~ m1_subset_1(sK9(X0,sK7,sK5),u1_struct_0(sK5)) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f260,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X2,X1,sK9(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( sK9(X0,sK7,sK5) = X1
        | ~ r2_lattice3(sK5,sK6,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK5))
        | sP0(X1,sK5,sK6)
        | sP2(X0,sK7,sK5)
        | ~ r2_lattice3(sK5,sK7,sK9(X0,sK7,sK5))
        | ~ m1_subset_1(sK9(X0,sK7,sK5),u1_struct_0(sK5)) )
    | ~ spl12_4 ),
    inference(resolution,[],[f259,f39])).

fof(f39,plain,(
    ! [X3] :
      ( r2_lattice3(sK5,sK6,X3)
      | ~ r2_lattice3(sK5,sK7,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_yellow_0(sK5,sK7)
    & r1_yellow_0(sK5,sK6)
    & ! [X3] :
        ( ( ( r2_lattice3(sK5,sK6,X3)
            | ~ r2_lattice3(sK5,sK7,X3) )
          & ( r2_lattice3(sK5,sK7,X3)
            | ~ r2_lattice3(sK5,sK6,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
    & l1_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f15,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & ! [X3] :
                ( ( ( r2_lattice3(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_yellow_0(sK5,X2)
          & r1_yellow_0(sK5,X1)
          & ! [X3] :
              ( ( ( r2_lattice3(sK5,X1,X3)
                  | ~ r2_lattice3(sK5,X2,X3) )
                & ( r2_lattice3(sK5,X2,X3)
                  | ~ r2_lattice3(sK5,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) )
      & l1_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2,X1] :
        ( ~ r1_yellow_0(sK5,X2)
        & r1_yellow_0(sK5,X1)
        & ! [X3] :
            ( ( ( r2_lattice3(sK5,X1,X3)
                | ~ r2_lattice3(sK5,X2,X3) )
              & ( r2_lattice3(sK5,X2,X3)
                | ~ r2_lattice3(sK5,X1,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) )
   => ( ~ r1_yellow_0(sK5,sK7)
      & r1_yellow_0(sK5,sK6)
      & ! [X3] :
          ( ( ( r2_lattice3(sK5,sK6,X3)
              | ~ r2_lattice3(sK5,sK7,X3) )
            & ( r2_lattice3(sK5,sK7,X3)
              | ~ r2_lattice3(sK5,sK6,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1)
          & ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r2_lattice3(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( r1_yellow_0(X0,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                  <=> r2_lattice3(X0,X2,X3) ) ) )
           => r1_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f259,plain,
    ( ! [X6,X7] :
        ( ~ r2_lattice3(sK5,sK6,sK9(X6,sK7,sK5))
        | sK9(X6,sK7,sK5) = X7
        | ~ r2_lattice3(sK5,sK6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK5))
        | sP0(X7,sK5,sK6)
        | sP2(X6,sK7,sK5) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f258,f50])).

fof(f258,plain,
    ( ! [X6,X7] :
        ( ~ r2_lattice3(sK5,sK6,sK9(X6,sK7,sK5))
        | ~ m1_subset_1(sK9(X6,sK7,sK5),u1_struct_0(sK5))
        | sK9(X6,sK7,sK5) = X7
        | ~ r2_lattice3(sK5,sK6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK5))
        | sP0(X7,sK5,sK6)
        | sP2(X6,sK7,sK5) )
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f249,f90])).

fof(f249,plain,(
    ! [X6,X7] :
      ( ~ r2_lattice3(sK5,sK6,sK9(X6,sK7,sK5))
      | ~ m1_subset_1(sK9(X6,sK7,sK5),u1_struct_0(sK5))
      | sK9(X6,sK7,sK5) = X7
      | ~ sP3(sK5,sK6)
      | ~ r2_lattice3(sK5,sK6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(sK5))
      | sP0(X7,sK5,sK6)
      | sP2(X6,sK7,sK5) ) ),
    inference(resolution,[],[f162,f224])).

fof(f224,plain,(
    ! [X2] :
      ( ~ sP0(sK9(X2,sK7,sK5),sK5,sK6)
      | sP2(X2,sK7,sK5) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X2] :
      ( sP2(X2,sK7,sK5)
      | ~ sP0(sK9(X2,sK7,sK5),sK5,sK6)
      | ~ sP0(sK9(X2,sK7,sK5),sK5,sK6) ) ),
    inference(resolution,[],[f221,f59])).

fof(f221,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK5,sK6,sK11(sK9(X2,sK7,sK5),sK5,X3))
      | sP2(X2,sK7,sK5)
      | ~ sP0(sK9(X2,sK7,sK5),sK5,X3) ) ),
    inference(subsumption_resolution,[],[f220,f58])).

fof(f220,plain,(
    ! [X2,X3] :
      ( ~ r2_lattice3(sK5,sK6,sK11(sK9(X2,sK7,sK5),sK5,X3))
      | ~ m1_subset_1(sK11(sK9(X2,sK7,sK5),sK5,X3),u1_struct_0(sK5))
      | sP2(X2,sK7,sK5)
      | ~ sP0(sK9(X2,sK7,sK5),sK5,X3) ) ),
    inference(resolution,[],[f218,f60])).

fof(f218,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK5,sK9(X0,sK7,sK5),X1)
      | ~ r2_lattice3(sK5,sK6,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | sP2(X0,sK7,sK5) ) ),
    inference(resolution,[],[f217,f54])).

fof(f217,plain,(
    ! [X2] :
      ( sP1(sK9(X2,sK7,sK5),sK5,sK6)
      | sP2(X2,sK7,sK5) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X2] :
      ( sP1(sK9(X2,sK7,sK5),sK5,sK6)
      | sP2(X2,sK7,sK5)
      | sP1(sK9(X2,sK7,sK5),sK5,sK6) ) ),
    inference(resolution,[],[f214,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK10(X0,X1,X2))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK5,sK6,sK10(sK9(X0,sK7,sK5),sK5,X1))
      | sP1(sK9(X0,sK7,sK5),sK5,X1)
      | sP2(X0,sK7,sK5) ) ),
    inference(subsumption_resolution,[],[f210,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f210,plain,(
    ! [X0,X1] :
      ( sP2(X0,sK7,sK5)
      | sP1(sK9(X0,sK7,sK5),sK5,X1)
      | ~ r2_lattice3(sK5,sK6,sK10(sK9(X0,sK7,sK5),sK5,X1))
      | ~ m1_subset_1(sK10(sK9(X0,sK7,sK5),sK5,X1),u1_struct_0(sK5)) ) ),
    inference(resolution,[],[f128,f38])).

fof(f38,plain,(
    ! [X3] :
      ( r2_lattice3(sK5,sK7,X3)
      | ~ r2_lattice3(sK5,sK6,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK5)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,X1,sK10(sK9(X2,X1,X0),X0,X3))
      | sP2(X2,X1,X0)
      | sP1(sK9(X2,X1,X0),X0,X3) ) ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,X1,sK10(sK9(X2,X1,X0),X0,X3))
      | ~ m1_subset_1(sK10(sK9(X2,X1,X0),X0,X3),u1_struct_0(X0))
      | sP2(X2,X1,X0)
      | sP1(sK9(X2,X1,X0),X0,X3) ) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK10(X0,X1,X2))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK9(X1,X2,X0),X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP2(X1,X2,X0) ) ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(sK9(X0,X1,X2),X2,X1)
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X1,X0,X3)
      | ~ r2_lattice3(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X0,X1)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 = X3
      | ~ sP3(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP0(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP0(X3,X0,X1)
      | ~ sP3(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP0(X2,X0,X1)
      | ~ sP3(X0,X1) ) ),
    inference(superposition,[],[f112,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( sK8(X1,X2) = X0
      | ~ r2_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP0(X0,X1,X2)
      | ~ sP3(X1,X2) ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP2(sK8(X0,X1),X1,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | sP0(X4,X2,X1)
      | ~ r2_lattice3(X2,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f856,plain,
    ( ! [X12,X11] :
        ( sK9(X11,sK7,sK5) != X12
        | sP0(X12,sK5,sK6)
        | ~ m1_subset_1(X12,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK6,X12)
        | sP2(X11,sK7,sK5) )
    | ~ spl12_27 ),
    inference(subsumption_resolution,[],[f855,f51])).

fof(f855,plain,
    ( ! [X12,X11] :
        ( ~ r2_lattice3(sK5,sK7,sK9(X11,sK7,sK5))
        | sK9(X11,sK7,sK5) != X12
        | sP0(X12,sK5,sK6)
        | ~ m1_subset_1(X12,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK6,X12)
        | sP2(X11,sK7,sK5) )
    | ~ spl12_27 ),
    inference(subsumption_resolution,[],[f832,f50])).

fof(f832,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(sK9(X11,sK7,sK5),u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK7,sK9(X11,sK7,sK5))
        | sK9(X11,sK7,sK5) != X12
        | sP0(X12,sK5,sK6)
        | ~ m1_subset_1(X12,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK6,X12)
        | sP2(X11,sK7,sK5) )
    | ~ spl12_27 ),
    inference(resolution,[],[f578,f213])).

fof(f213,plain,(
    ! [X6,X4,X5] :
      ( sP1(sK9(X4,X5,X6),X6,X5)
      | sP2(X4,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,(
    ! [X6,X4,X5] :
      ( sP2(X4,X5,X6)
      | sP1(sK9(X4,X5,X6),X6,X5)
      | sP1(sK9(X4,X5,X6),X6,X5) ) ),
    inference(resolution,[],[f128,f56])).

fof(f578,plain,
    ( ! [X4,X3] :
        ( ~ sP1(X3,sK5,sK7)
        | ~ m1_subset_1(X3,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK7,X3)
        | X3 != X4
        | sP0(X4,sK5,sK6)
        | ~ m1_subset_1(X4,u1_struct_0(sK5))
        | ~ r2_lattice3(sK5,sK6,X4) )
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f577])).

fof(f598,plain,(
    ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f596,f37])).

fof(f37,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f596,plain,
    ( ~ l1_orders_2(sK5)
    | ~ spl12_2 ),
    inference(resolution,[],[f595,f62])).

fof(f62,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f13,f12,f11,f10,f9])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> sP3(X0,X1) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_0)).

fof(f595,plain,
    ( ~ sP4(sK5)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f594,f41])).

fof(f41,plain,(
    ~ r1_yellow_0(sK5,sK7) ),
    inference(cnf_transformation,[],[f18])).

fof(f594,plain,
    ( r1_yellow_0(sK5,sK7)
    | ~ sP4(sK5)
    | ~ spl12_2 ),
    inference(resolution,[],[f81,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | r1_yellow_0(X0,X1)
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ~ sP3(X0,X1) )
          & ( sP3(X0,X1)
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f81,plain,
    ( sP3(sK5,sK7)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f80])).

% (7651)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f80,plain,
    ( spl12_2
  <=> sP3(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f579,plain,
    ( spl12_2
    | spl12_27
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f546,f89,f577,f80])).

fof(f546,plain,
    ( ! [X4,X3] :
        ( X3 != X4
        | ~ r2_lattice3(sK5,sK6,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK5))
        | sP0(X4,sK5,sK6)
        | sP3(sK5,sK7)
        | ~ sP1(X3,sK5,sK7)
        | ~ r2_lattice3(sK5,sK7,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK5)) )
    | ~ spl12_4 ),
    inference(resolution,[],[f283,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X2,X1,X0)
      | sP3(X0,X1)
      | ~ sP1(X2,X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f283,plain,
    ( ! [X26,X25] :
        ( sP2(X25,sK7,sK5)
        | X25 != X26
        | ~ r2_lattice3(sK5,sK6,X26)
        | ~ m1_subset_1(X26,u1_struct_0(sK5))
        | sP0(X26,sK5,sK6) )
    | ~ spl12_4 ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( ! [X26,X25] :
        ( X25 != X26
        | sP2(X25,sK7,sK5)
        | ~ r2_lattice3(sK5,sK6,X26)
        | ~ m1_subset_1(X26,u1_struct_0(sK5))
        | sP0(X26,sK5,sK6)
        | sP2(X25,sK7,sK5) )
    | ~ spl12_4 ),
    inference(superposition,[],[f53,f262])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) != X0
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f574,plain,
    ( ~ spl12_4
    | spl12_25 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl12_4
    | spl12_25 ),
    inference(subsumption_resolution,[],[f567,f90])).

fof(f567,plain,
    ( ~ sP3(sK5,sK6)
    | spl12_25 ),
    inference(resolution,[],[f561,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK8(X0,X1))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f561,plain,
    ( ~ r2_lattice3(sK5,sK6,sK8(sK5,sK6))
    | spl12_25 ),
    inference(avatar_component_clause,[],[f559])).

fof(f394,plain,
    ( ~ spl12_4
    | ~ spl12_7
    | spl12_8 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_7
    | spl12_8 ),
    inference(subsumption_resolution,[],[f390,f90])).

fof(f390,plain,
    ( ~ sP3(sK5,sK6)
    | ~ spl12_7
    | spl12_8 ),
    inference(resolution,[],[f386,f45])).

fof(f386,plain,
    ( ~ r2_lattice3(sK5,sK6,sK8(sK5,sK6))
    | ~ spl12_7
    | spl12_8 ),
    inference(subsumption_resolution,[],[f384,f316])).

fof(f384,plain,
    ( ~ r2_lattice3(sK5,sK6,sK8(sK5,sK6))
    | ~ m1_subset_1(sK8(sK5,sK6),u1_struct_0(sK5))
    | spl12_8 ),
    inference(resolution,[],[f321,f38])).

fof(f321,plain,
    ( ~ r2_lattice3(sK5,sK7,sK8(sK5,sK6))
    | spl12_8 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl12_8
  <=> r2_lattice3(sK5,sK7,sK8(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f329,plain,
    ( ~ spl12_4
    | spl12_7 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl12_4
    | spl12_7 ),
    inference(subsumption_resolution,[],[f325,f90])).

fof(f325,plain,
    ( ~ sP3(sK5,sK6)
    | spl12_7 ),
    inference(resolution,[],[f317,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f317,plain,
    ( ~ m1_subset_1(sK8(sK5,sK6),u1_struct_0(sK5))
    | spl12_7 ),
    inference(avatar_component_clause,[],[f315])).

fof(f322,plain,
    ( ~ spl12_7
    | ~ spl12_8
    | spl12_2
    | ~ spl12_3
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f306,f296,f86,f80,f319,f315])).

fof(f86,plain,
    ( spl12_3
  <=> ! [X1] :
        ( sP1(sK8(sK5,sK6),sK5,X1)
        | ~ r2_lattice3(sK5,sK7,sK10(sK8(sK5,sK6),sK5,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f306,plain,
    ( ~ r2_lattice3(sK5,sK7,sK8(sK5,sK6))
    | ~ m1_subset_1(sK8(sK5,sK6),u1_struct_0(sK5))
    | spl12_2
    | ~ spl12_3
    | ~ spl12_5 ),
    inference(resolution,[],[f305,f103])).

fof(f103,plain,
    ( sP1(sK8(sK5,sK6),sK5,sK7)
    | ~ spl12_3 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( sP1(sK8(sK5,sK6),sK5,sK7)
    | sP1(sK8(sK5,sK6),sK5,sK7)
    | ~ spl12_3 ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK5,sK7,sK10(sK8(sK5,sK6),sK5,X1))
        | sP1(sK8(sK5,sK6),sK5,X1) )
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f305,plain,
    ( ! [X2] :
        ( ~ sP1(X2,sK5,sK7)
        | ~ r2_lattice3(sK5,sK7,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK5)) )
    | spl12_2
    | ~ spl12_5 ),
    inference(subsumption_resolution,[],[f304,f82])).

fof(f82,plain,
    ( ~ sP3(sK5,sK7)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f304,plain,
    ( ! [X2] :
        ( sP3(sK5,sK7)
        | ~ sP1(X2,sK5,sK7)
        | ~ r2_lattice3(sK5,sK7,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK5)) )
    | ~ spl12_5 ),
    inference(resolution,[],[f297,f48])).

fof(f297,plain,
    ( ! [X0] : sP2(X0,sK7,sK5)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f296])).

fof(f99,plain,(
    spl12_4 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl12_4 ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( ~ l1_orders_2(sK5)
    | spl12_4 ),
    inference(resolution,[],[f95,f62])).

fof(f95,plain,
    ( ~ sP4(sK5)
    | spl12_4 ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f40,plain,(
    r1_yellow_0(sK5,sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,
    ( ~ r1_yellow_0(sK5,sK6)
    | ~ sP4(sK5)
    | spl12_4 ),
    inference(resolution,[],[f91,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | ~ r1_yellow_0(X0,X1)
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,
    ( ~ sP3(sK5,sK6)
    | spl12_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f92,plain,
    ( spl12_3
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f84,f89,f86])).

fof(f84,plain,(
    ! [X1] :
      ( ~ sP3(sK5,sK6)
      | sP1(sK8(sK5,sK6),sK5,X1)
      | ~ r2_lattice3(sK5,sK7,sK10(sK8(sK5,sK6),sK5,X1)) ) ),
    inference(subsumption_resolution,[],[f72,f55])).

fof(f72,plain,(
    ! [X1] :
      ( ~ sP3(sK5,sK6)
      | sP1(sK8(sK5,sK6),sK5,X1)
      | ~ r2_lattice3(sK5,sK7,sK10(sK8(sK5,sK6),sK5,X1))
      | ~ m1_subset_1(sK10(sK8(sK5,sK6),sK5,X1),u1_struct_0(sK5)) ) ),
    inference(resolution,[],[f69,f39])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK10(sK8(X0,X1),X0,X2))
      | ~ sP3(X0,X1)
      | sP1(sK8(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f67,f55])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK10(sK8(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,sK10(sK8(X0,X1),X0,X2))
      | ~ sP3(X0,X1)
      | sP1(sK8(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f65,f57])).

%------------------------------------------------------------------------------
