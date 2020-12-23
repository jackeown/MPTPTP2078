%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1537+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 328 expanded)
%              Number of leaves         :   26 ( 116 expanded)
%              Depth                    :   26
%              Number of atoms          :  713 (2009 expanded)
%              Number of equality atoms :   34 (  62 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (25726)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (25749)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (25739)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (25724)Refutation not found, incomplete strategy% (25724)------------------------------
% (25724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f221,f226,f235,f248,f253,f260,f263])).

fof(f263,plain,
    ( spl14_1
    | ~ spl14_6
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f262,f223,f154,f80])).

fof(f80,plain,
    ( spl14_1
  <=> r1_yellow_0(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f154,plain,
    ( spl14_6
  <=> sP4(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f223,plain,
    ( spl14_8
  <=> sP5(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f262,plain,
    ( r1_yellow_0(sK7,sK8)
    | ~ spl14_6
    | ~ spl14_8 ),
    inference(subsumption_resolution,[],[f236,f224])).

fof(f224,plain,
    ( sP5(sK7)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f223])).

fof(f236,plain,
    ( r1_yellow_0(sK7,sK8)
    | ~ sP5(sK7)
    | ~ spl14_6 ),
    inference(resolution,[],[f155,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | r1_yellow_0(X0,X1)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ~ sP4(X0,X1) )
          & ( sP4(X0,X1)
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ sP5(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> sP4(X0,X1) )
      | ~ sP5(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f155,plain,
    ( sP4(sK7,sK8)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f260,plain,
    ( ~ spl14_6
    | spl14_11 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl14_6
    | spl14_11 ),
    inference(subsumption_resolution,[],[f256,f155])).

fof(f256,plain,
    ( ~ sP4(sK7,sK8)
    | spl14_11 ),
    inference(resolution,[],[f247,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ! [X2] :
            ( ~ sP3(X2,X1,X0)
            | ~ sP2(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ( sP3(sK10(X0,X1),X1,X0)
          & sP2(sK10(X0,X1),X0,X1)
          & r2_lattice3(X0,X1,sK10(X0,X1))
          & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) )
        | ~ sP4(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( sP3(X3,X1,X0)
          & sP2(X3,X0,X1)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sP3(sK10(X0,X1),X1,X0)
        & sP2(sK10(X0,X1),X0,X1)
        & r2_lattice3(X0,X1,sK10(X0,X1))
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ! [X2] :
            ( ~ sP3(X2,X1,X0)
            | ~ sP2(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X3] :
            ( sP3(X3,X1,X0)
            & sP2(X3,X0,X1)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP4(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ! [X2] :
            ( ~ sP3(X2,X1,X0)
            | ~ sP2(X2,X0,X1)
            | ~ r2_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP3(X2,X1,X0)
            & sP2(X2,X0,X1)
            & r2_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ? [X2] :
          ( sP3(X2,X1,X0)
          & sP2(X2,X0,X1)
          & r2_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f247,plain,
    ( ~ m1_subset_1(sK10(sK7,sK8),u1_struct_0(sK7))
    | spl14_11 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl14_11
  <=> m1_subset_1(sK10(sK7,sK8),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f253,plain,
    ( ~ spl14_6
    | spl14_10 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl14_6
    | spl14_10 ),
    inference(subsumption_resolution,[],[f249,f155])).

fof(f249,plain,
    ( ~ sP4(sK7,sK8)
    | spl14_10 ),
    inference(resolution,[],[f243,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK10(X0,X1))
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f243,plain,
    ( ~ r2_lattice3(sK7,sK8,sK10(sK7,sK8))
    | spl14_10 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl14_10
  <=> r2_lattice3(sK7,sK8,sK10(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f248,plain,
    ( ~ spl14_10
    | ~ spl14_11
    | ~ spl14_2
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f239,f154,f84,f245,f241])).

fof(f84,plain,
    ( spl14_2
  <=> ! [X2] :
        ( ~ sP0(X2,sK7,sK8)
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f239,plain,
    ( ~ m1_subset_1(sK10(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_lattice3(sK7,sK8,sK10(sK7,sK8))
    | ~ spl14_2
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f238,f155])).

fof(f238,plain,
    ( ~ m1_subset_1(sK10(sK7,sK8),u1_struct_0(sK7))
    | ~ r2_lattice3(sK7,sK8,sK10(sK7,sK8))
    | ~ sP4(sK7,sK8)
    | ~ spl14_2 ),
    inference(resolution,[],[f85,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( sP0(sK10(X0,X1),X0,X1)
      | ~ sP4(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | sP0(sK10(X0,X1),X0,X1)
      | sP0(sK10(X0,X1),X0,X1) ) ),
    inference(resolution,[],[f124,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK6(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
          & r2_lattice3(X1,X2,sK6(X0,X1,X2))
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
        & r2_lattice3(X1,X2,sK6(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X2,X3)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK6(sK10(X0,X1),X0,X2))
      | ~ sP4(X0,X1)
      | sP0(sK10(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f121,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(sK10(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,sK6(sK10(X0,X1),X0,X2))
      | ~ sP4(X0,X1)
      | sP0(sK10(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f113,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK10(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP2(sK10(X0,X1),X0,X1)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
          & r2_lattice3(X1,X2,sK12(X0,X1,X2))
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X0,X3)
          & r2_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
        & r2_lattice3(X1,X2,sK12(X0,X1,X2))
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X0,X3)
            & r2_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X0,X4)
            | ~ r2_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X5] :
            ( ~ r1_orders_2(X0,X2,X5)
            & r2_lattice3(X0,X1,X5)
            & m1_subset_1(X5,u1_struct_0(X0)) ) )
      & ( ! [X5] :
            ( r1_orders_2(X0,X2,X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X5] :
          ( r1_orders_2(X0,X2,X5)
          | ~ r2_lattice3(X0,X1,X5)
          | ~ m1_subset_1(X5,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f85,plain,
    ( ! [X2] :
        ( ~ sP0(X2,sK7,sK8)
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,X2) )
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f235,plain,(
    spl14_8 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl14_8 ),
    inference(subsumption_resolution,[],[f233,f52])).

fof(f52,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ! [X2] :
          ( ~ sP0(X2,sK7,sK8)
          | ~ r2_lattice3(sK7,sK8,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
      | ~ r1_yellow_0(sK7,sK8) )
    & ( ( sP0(sK9,sK7,sK8)
        & r2_lattice3(sK7,sK8,sK9)
        & m1_subset_1(sK9,u1_struct_0(sK7)) )
      | r1_yellow_0(sK7,sK8) )
    & l1_orders_2(sK7)
    & v5_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( ~ sP0(X2,X0,X1)
                  | ~ r2_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r1_yellow_0(X0,X1) )
            & ( ? [X3] :
                  ( sP0(X3,X0,X1)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | r1_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( ~ sP0(X2,sK7,X1)
                | ~ r2_lattice3(sK7,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
            | ~ r1_yellow_0(sK7,X1) )
          & ( ? [X3] :
                ( sP0(X3,sK7,X1)
                & r2_lattice3(sK7,X1,X3)
                & m1_subset_1(X3,u1_struct_0(sK7)) )
            | r1_yellow_0(sK7,X1) ) )
      & l1_orders_2(sK7)
      & v5_orders_2(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( ! [X2] :
              ( ~ sP0(X2,sK7,X1)
              | ~ r2_lattice3(sK7,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
          | ~ r1_yellow_0(sK7,X1) )
        & ( ? [X3] :
              ( sP0(X3,sK7,X1)
              & r2_lattice3(sK7,X1,X3)
              & m1_subset_1(X3,u1_struct_0(sK7)) )
          | r1_yellow_0(sK7,X1) ) )
   => ( ( ! [X2] :
            ( ~ sP0(X2,sK7,sK8)
            | ~ r2_lattice3(sK7,sK8,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
        | ~ r1_yellow_0(sK7,sK8) )
      & ( ? [X3] :
            ( sP0(X3,sK7,sK8)
            & r2_lattice3(sK7,sK8,X3)
            & m1_subset_1(X3,u1_struct_0(sK7)) )
        | r1_yellow_0(sK7,sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( sP0(X3,sK7,sK8)
        & r2_lattice3(sK7,sK8,X3)
        & m1_subset_1(X3,u1_struct_0(sK7)) )
   => ( sP0(sK9,sK7,sK8)
      & r2_lattice3(sK7,sK8,sK9)
      & m1_subset_1(sK9,u1_struct_0(sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X3] :
                ( sP0(X3,X0,X1)
                & r2_lattice3(X0,X1,X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ~ sP0(X2,X0,X1)
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) )
          & ( ? [X2] :
                ( sP0(X2,X0,X1)
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r1_yellow_0(X0,X1)
        <~> ? [X2] :
              ( sP0(X2,X0,X1)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f7,f12])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r1_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r1_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f233,plain,
    ( ~ l1_orders_2(sK7)
    | spl14_8 ),
    inference(resolution,[],[f225,f77])).

fof(f77,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f9,f18,f17,f16,f15,f14])).

fof(f14,plain,(
    ! [X3,X0,X1] :
      ( sP1(X3,X0,X1)
    <=> ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( sP3(X2,X1,X0)
    <=> ! [X3] :
          ( X2 = X3
          | sP1(X3,X0,X1)
          | ~ r2_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
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

fof(f225,plain,
    ( ~ sP5(sK7)
    | spl14_8 ),
    inference(avatar_component_clause,[],[f223])).

fof(f226,plain,
    ( ~ spl14_8
    | ~ spl14_1
    | spl14_6 ),
    inference(avatar_split_clause,[],[f162,f154,f80,f223])).

fof(f162,plain,
    ( ~ r1_yellow_0(sK7,sK8)
    | ~ sP5(sK7)
    | spl14_6 ),
    inference(resolution,[],[f156,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ r1_yellow_0(X0,X1)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f156,plain,
    ( ~ sP4(sK7,sK8)
    | spl14_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f221,plain,
    ( ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5
    | spl14_6 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5
    | spl14_6 ),
    inference(subsumption_resolution,[],[f219,f100])).

fof(f100,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl14_5
  <=> m1_subset_1(sK9,u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f219,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5
    | spl14_6 ),
    inference(subsumption_resolution,[],[f218,f95])).

fof(f95,plain,
    ( r2_lattice3(sK7,sK8,sK9)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl14_4
  <=> r2_lattice3(sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f218,plain,
    ( ~ r2_lattice3(sK7,sK8,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5
    | spl14_6 ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,
    ( sK9 != sK9
    | ~ r2_lattice3(sK7,sK8,sK9)
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5
    | spl14_6 ),
    inference(resolution,[],[f215,f115])).

fof(f115,plain,
    ( sP2(sK9,sK7,sK8)
    | ~ spl14_3 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( sP2(sK9,sK7,sK8)
    | sP2(sK9,sK7,sK8)
    | ~ spl14_3 ),
    inference(resolution,[],[f109,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X1,X2,sK12(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK7,sK8,sK12(sK9,sK7,X1))
        | sP2(sK9,sK7,X1) )
    | ~ spl14_3 ),
    inference(subsumption_resolution,[],[f106,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK12(sK9,sK7,X1),u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,sK12(sK9,sK7,X1))
        | sP2(sK9,sK7,X1) )
    | ~ spl14_3 ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,sK12(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,
    ( ! [X0] :
        ( r1_orders_2(sK7,sK9,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,X0) )
    | ~ spl14_3 ),
    inference(resolution,[],[f47,f90])).

fof(f90,plain,
    ( sP0(sK9,sK7,sK8)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl14_3
  <=> sP0(sK9,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f215,plain,
    ( ! [X2] :
        ( ~ sP2(X2,sK7,sK8)
        | sK9 != X2
        | ~ r2_lattice3(sK7,sK8,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5
    | spl14_6 ),
    inference(subsumption_resolution,[],[f214,f156])).

fof(f214,plain,
    ( ! [X2] :
        ( sK9 != X2
        | sP4(sK7,sK8)
        | ~ sP2(X2,sK7,sK8)
        | ~ r2_lattice3(sK7,sK8,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(resolution,[],[f184,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X0)
      | sP4(X0,X1)
      | ~ sP2(X2,X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f184,plain,
    ( ! [X6] :
        ( sP3(X6,sK8,sK7)
        | sK9 != X6 )
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X6] :
        ( sK9 != X6
        | sP3(X6,sK8,sK7)
        | sP3(X6,sK8,sK7) )
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(superposition,[],[f68,f177])).

fof(f177,plain,
    ( ! [X0] :
        ( sK9 = sK11(X0,sK8,sK7)
        | sP3(X0,sK8,sK7) )
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f176,f95])).

fof(f176,plain,
    ( ! [X0] :
        ( sP3(X0,sK8,sK7)
        | sK9 = sK11(X0,sK8,sK7)
        | ~ r2_lattice3(sK7,sK8,sK9) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,
    ( ! [X0] :
        ( sP3(X0,sK8,sK7)
        | sK9 = sK11(X0,sK8,sK7)
        | ~ r2_lattice3(sK7,sK8,sK9)
        | sP3(X0,sK8,sK7) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(resolution,[],[f174,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X2,X1,sK11(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( sK11(X0,X1,X2) != X0
          & ~ sP1(sK11(X0,X1,X2),X2,X1)
          & r2_lattice3(X2,X1,sK11(X0,X1,X2))
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( X0 = X4
            | sP1(X4,X2,X1)
            | ~ r2_lattice3(X2,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ~ sP1(X3,X2,X1)
          & r2_lattice3(X2,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( sK11(X0,X1,X2) != X0
        & ~ sP1(sK11(X0,X1,X2),X2,X1)
        & r2_lattice3(X2,X1,sK11(X0,X1,X2))
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ~ sP1(X3,X2,X1)
            & r2_lattice3(X2,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ! [X4] :
            ( X0 = X4
            | sP1(X4,X2,X1)
            | ~ r2_lattice3(X2,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

% (25748)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (25724)Termination reason: Refutation not found, incomplete strategy
% (25733)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark

% (25724)Memory used [KB]: 10618
% (25724)Time elapsed: 0.109 s
% (25724)------------------------------
% (25724)------------------------------
fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ( sP3(X2,X1,X0)
        | ? [X3] :
            ( X2 != X3
            & ~ sP1(X3,X0,X1)
            & r2_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | sP1(X3,X0,X1)
            | ~ r2_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f174,plain,
    ( ! [X17,X16] :
        ( ~ r2_lattice3(sK7,sK8,sK11(X17,X16,sK7))
        | sP3(X17,X16,sK7)
        | sK9 = sK11(X17,X16,sK7)
        | ~ r2_lattice3(sK7,X16,sK9) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f173,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f173,plain,
    ( ! [X17,X16] :
        ( ~ r2_lattice3(sK7,X16,sK9)
        | sP3(X17,X16,sK7)
        | sK9 = sK11(X17,X16,sK7)
        | ~ m1_subset_1(sK11(X17,X16,sK7),u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,sK11(X17,X16,sK7)) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f167,f100])).

fof(f167,plain,
    ( ! [X17,X16] :
        ( ~ r2_lattice3(sK7,X16,sK9)
        | ~ m1_subset_1(sK9,u1_struct_0(sK7))
        | sP3(X17,X16,sK7)
        | sK9 = sK11(X17,X16,sK7)
        | ~ m1_subset_1(sK11(X17,X16,sK7),u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,sK11(X17,X16,sK7)) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(resolution,[],[f119,f143])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK7,X0,sK9)
        | sK9 = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,X0) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f142,f51])).

fof(f51,plain,(
    v5_orders_2(sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f142,plain,
    ( ! [X0] :
        ( sK9 = X0
        | ~ r1_orders_2(sK7,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ v5_orders_2(sK7)
        | ~ r2_lattice3(sK7,sK8,X0) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f141,f52])).

fof(f141,plain,
    ( ! [X0] :
        ( sK9 = X0
        | ~ r1_orders_2(sK7,X0,sK9)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ l1_orders_2(sK7)
        | ~ v5_orders_2(sK7)
        | ~ r2_lattice3(sK7,sK8,X0) )
    | ~ spl14_3
    | ~ spl14_5 ),
    inference(subsumption_resolution,[],[f140,f100])).

fof(f140,plain,
    ( ! [X0] :
        ( sK9 = X0
        | ~ r1_orders_2(sK7,X0,sK9)
        | ~ m1_subset_1(sK9,u1_struct_0(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ l1_orders_2(sK7)
        | ~ v5_orders_2(sK7)
        | ~ r2_lattice3(sK7,sK8,X0) )
    | ~ spl14_3 ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( ! [X0] :
        ( sK9 = X0
        | ~ r1_orders_2(sK7,X0,sK9)
        | ~ m1_subset_1(sK9,u1_struct_0(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ l1_orders_2(sK7)
        | ~ v5_orders_2(sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ r2_lattice3(sK7,sK8,X0) )
    | ~ spl14_3 ),
    inference(resolution,[],[f78,f104])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK11(X1,X2,X0),X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP3(X1,X2,X0) ) ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(sK11(X0,X1,X2),X2,X1)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | r1_orders_2(X1,X0,X3)
      | ~ r2_lattice3(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( r1_orders_2(X1,X0,X3)
            | ~ r2_lattice3(X1,X2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( ~ r1_orders_2(X1,X0,sK13(X0,X1,X2))
          & r2_lattice3(X1,X2,sK13(X0,X1,X2))
          & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X0,X4)
          & r2_lattice3(X1,X2,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK13(X0,X1,X2))
        & r2_lattice3(X1,X2,sK13(X0,X1,X2))
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( r1_orders_2(X1,X0,X3)
            | ~ r2_lattice3(X1,X2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( ~ r1_orders_2(X1,X0,X4)
            & r2_lattice3(X1,X2,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X3,X0,X1] :
      ( ( sP1(X3,X0,X1)
        | ! [X4] :
            ( r1_orders_2(X0,X3,X4)
            | ~ r2_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
      & ( ? [X4] :
            ( ~ r1_orders_2(X0,X3,X4)
            & r2_lattice3(X0,X1,X4)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP1(X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sK11(X0,X1,X2) != X0
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,
    ( spl14_1
    | spl14_5 ),
    inference(avatar_split_clause,[],[f53,f98,f80])).

fof(f53,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7))
    | r1_yellow_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,
    ( spl14_1
    | spl14_4 ),
    inference(avatar_split_clause,[],[f54,f93,f80])).

fof(f54,plain,
    ( r2_lattice3(sK7,sK8,sK9)
    | r1_yellow_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,
    ( spl14_1
    | spl14_3 ),
    inference(avatar_split_clause,[],[f55,f88,f80])).

fof(f55,plain,
    ( sP0(sK9,sK7,sK8)
    | r1_yellow_0(sK7,sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,
    ( ~ spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f56,f84,f80])).

fof(f56,plain,(
    ! [X2] :
      ( ~ sP0(X2,sK7,sK8)
      | ~ r2_lattice3(sK7,sK8,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK7))
      | ~ r1_yellow_0(sK7,sK8) ) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
