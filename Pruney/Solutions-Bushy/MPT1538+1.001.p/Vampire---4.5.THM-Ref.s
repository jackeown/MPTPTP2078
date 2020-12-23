%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1538+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 (1704 expanded)
%              Number of leaves         :   14 ( 633 expanded)
%              Depth                    :   32
%              Number of atoms          :  582 (17162 expanded)
%              Number of equality atoms :   26 ( 423 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(subsumption_resolution,[],[f701,f476])).

fof(f476,plain,(
    r2_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f475,f36])).

fof(f36,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ! [X2] :
          ( ( ~ r1_orders_2(sK3,sK5(X2),X2)
            & r1_lattice3(sK3,sK4,sK5(X2))
            & m1_subset_1(sK5(X2),u1_struct_0(sK3)) )
          | ~ r1_lattice3(sK3,sK4,X2)
          | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
      | ~ r2_yellow_0(sK3,sK4) )
    & ( ( ! [X5] :
            ( r1_orders_2(sK3,X5,sK6)
            | ~ r1_lattice3(sK3,sK4,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
        & r1_lattice3(sK3,sK4,sK6)
        & m1_subset_1(sK6,u1_struct_0(sK3)) )
      | r2_yellow_0(sK3,sK4) )
    & l1_orders_2(sK3)
    & v5_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f17,f21,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r2_yellow_0(X0,X1) )
            & ( ? [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X4)
                      | ~ r1_lattice3(X0,X1,X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | r2_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(sK3,X3,X2)
                    & r1_lattice3(sK3,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(sK3)) )
                | ~ r1_lattice3(sK3,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
            | ~ r2_yellow_0(sK3,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(sK3,X5,X4)
                    | ~ r1_lattice3(sK3,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
                & r1_lattice3(sK3,X1,X4)
                & m1_subset_1(X4,u1_struct_0(sK3)) )
            | r2_yellow_0(sK3,X1) ) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ( ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(sK3,X3,X2)
                  & r1_lattice3(sK3,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              | ~ r1_lattice3(sK3,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
          | ~ r2_yellow_0(sK3,X1) )
        & ( ? [X4] :
              ( ! [X5] :
                  ( r1_orders_2(sK3,X5,X4)
                  | ~ r1_lattice3(sK3,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
              & r1_lattice3(sK3,X1,X4)
              & m1_subset_1(X4,u1_struct_0(sK3)) )
          | r2_yellow_0(sK3,X1) ) )
   => ( ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(sK3,X3,X2)
                & r1_lattice3(sK3,sK4,X3)
                & m1_subset_1(X3,u1_struct_0(sK3)) )
            | ~ r1_lattice3(sK3,sK4,X2)
            | ~ m1_subset_1(X2,u1_struct_0(sK3)) )
        | ~ r2_yellow_0(sK3,sK4) )
      & ( ? [X4] :
            ( ! [X5] :
                ( r1_orders_2(sK3,X5,X4)
                | ~ r1_lattice3(sK3,sK4,X5)
                | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
            & r1_lattice3(sK3,sK4,X4)
            & m1_subset_1(X4,u1_struct_0(sK3)) )
        | r2_yellow_0(sK3,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(sK3,X3,X2)
          & r1_lattice3(sK3,sK4,X3)
          & m1_subset_1(X3,u1_struct_0(sK3)) )
     => ( ~ r1_orders_2(sK3,sK5(X2),X2)
        & r1_lattice3(sK3,sK4,sK5(X2))
        & m1_subset_1(sK5(X2),u1_struct_0(sK3)) ) ) ),
    introduced(choice_axiom,[])).

% (5880)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f21,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( r1_orders_2(sK3,X5,X4)
            | ~ r1_lattice3(sK3,sK4,X5)
            | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
        & r1_lattice3(sK3,sK4,X4)
        & m1_subset_1(X4,u1_struct_0(sK3)) )
   => ( ! [X5] :
          ( r1_orders_2(sK3,X5,sK6)
          | ~ r1_lattice3(sK3,sK4,X5)
          | ~ m1_subset_1(X5,u1_struct_0(sK3)) )
      & r1_lattice3(sK3,sK4,sK6)
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | r2_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_yellow_0(X0,X1)
        <~> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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

fof(f475,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f474,f37])).

fof(f37,plain,
    ( r1_lattice3(sK3,sK4,sK6)
    | r2_yellow_0(sK3,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f474,plain,
    ( ~ r1_lattice3(sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f473,f286])).

fof(f286,plain,
    ( sP0(sK6,sK3,sK4)
    | r2_yellow_0(sK3,sK4) ),
    inference(equality_resolution,[],[f248])).

fof(f248,plain,(
    ! [X6] :
      ( sK6 != X6
      | sP0(X6,sK3,sK4)
      | r2_yellow_0(sK3,sK4) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X6] :
      ( sK6 != X6
      | sP0(X6,sK3,sK4)
      | sP0(X6,sK3,sK4)
      | r2_yellow_0(sK3,sK4) ) ),
    inference(superposition,[],[f57,f189])).

fof(f189,plain,(
    ! [X0] :
      ( sK6 = sK9(X0,sK3,sK4)
      | sP0(X0,sK3,sK4)
      | r2_yellow_0(sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f188,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( sK9(X0,X1,X2) != X0
          & ! [X4] :
              ( r1_orders_2(X1,X4,sK9(X0,X1,X2))
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,sK9(X0,X1,X2))
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ( ~ r1_orders_2(X1,sK10(X1,X2,X5),X5)
              & r1_lattice3(X1,X2,sK10(X1,X2,X5))
              & m1_subset_1(sK10(X1,X2,X5),u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f30,f32,f31])).

% (5899)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X0 != X3
          & ! [X4] :
              ( r1_orders_2(X1,X4,X3)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( sK9(X0,X1,X2) != X0
        & ! [X4] :
            ( r1_orders_2(X1,X4,sK9(X0,X1,X2))
            | ~ r1_lattice3(X1,X2,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r1_lattice3(X1,X2,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( ~ r1_orders_2(X1,X6,X5)
          & r1_lattice3(X1,X2,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK10(X1,X2,X5),X5)
        & r1_lattice3(X1,X2,sK10(X1,X2,X5))
        & m1_subset_1(sK10(X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( X0 != X3
            & ! [X4] :
                ( r1_orders_2(X1,X4,X3)
                | ~ r1_lattice3(X1,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( X0 = X5
            | ? [X6] :
                ( ~ r1_orders_2(X1,X6,X5)
                & r1_lattice3(X1,X2,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X2,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( X2 != X3
            & ! [X4] :
                ( r1_orders_2(X0,X4,X3)
                | ~ r1_lattice3(X0,X1,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( X2 = X3
            | ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( X2 = X3
          | ? [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              & r1_lattice3(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r1_lattice3(X0,X1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f188,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,sK4)
      | sP0(X0,sK3,sK4)
      | sK6 = sK9(X0,sK3,sK4)
      | ~ m1_subset_1(sK9(X0,sK3,sK4),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f187,f36])).

fof(f187,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,sK4)
      | sP0(X0,sK3,sK4)
      | sK6 = sK9(X0,sK3,sK4)
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK9(X0,sK3,sK4),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f186,f93])).

fof(f93,plain,(
    ! [X3] :
      ( r1_orders_2(sK3,sK6,sK9(X3,sK3,sK4))
      | sP0(X3,sK3,sK4)
      | r2_yellow_0(sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f85,plain,(
    ! [X3] :
      ( r2_yellow_0(sK3,sK4)
      | sP0(X3,sK3,sK4)
      | r1_orders_2(sK3,sK6,sK9(X3,sK3,sK4))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f37,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_orders_2(X1,X4,sK9(X0,X1,X2))
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f186,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,sK4)
      | sP0(X0,sK3,sK4)
      | sK6 = sK9(X0,sK3,sK4)
      | ~ r1_orders_2(sK3,sK6,sK9(X0,sK3,sK4))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK9(X0,sK3,sK4),u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f185,f34])).

fof(f34,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f185,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,sK4)
      | sP0(X0,sK3,sK4)
      | sK6 = sK9(X0,sK3,sK4)
      | ~ r1_orders_2(sK3,sK6,sK9(X0,sK3,sK4))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK9(X0,sK3,sK4),u1_struct_0(sK3))
      | ~ v5_orders_2(sK3) ) ),
    inference(subsumption_resolution,[],[f183,f35])).

fof(f35,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f183,plain,(
    ! [X0] :
      ( r2_yellow_0(sK3,sK4)
      | sP0(X0,sK3,sK4)
      | sK6 = sK9(X0,sK3,sK4)
      | ~ r1_orders_2(sK3,sK6,sK9(X0,sK3,sK4))
      | ~ m1_subset_1(sK6,u1_struct_0(sK3))
      | ~ m1_subset_1(sK9(X0,sK3,sK4),u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ v5_orders_2(sK3) ) ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f103,plain,(
    ! [X1] :
      ( r1_orders_2(sK3,sK9(X1,sK3,sK4),sK6)
      | r2_yellow_0(sK3,sK4)
      | sP0(X1,sK3,sK4) ) ),
    inference(subsumption_resolution,[],[f97,f54])).

fof(f97,plain,(
    ! [X1] :
      ( r1_orders_2(sK3,sK9(X1,sK3,sK4),sK6)
      | ~ m1_subset_1(sK9(X1,sK3,sK4),u1_struct_0(sK3))
      | r2_yellow_0(sK3,sK4)
      | sP0(X1,sK3,sK4) ) ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r1_lattice3(X1,X2,sK9(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f38,plain,(
    ! [X5] :
      ( ~ r1_lattice3(sK3,sK4,X5)
      | r1_orders_2(sK3,X5,sK6)
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | r2_yellow_0(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | sK9(X0,X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f473,plain,
    ( ~ sP0(sK6,sK3,sK4)
    | ~ r1_lattice3(sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f471,f106])).

fof(f106,plain,(
    ! [X1] :
      ( ~ sP1(X1,sK3)
      | r2_yellow_0(sK3,X1) ) ),
    inference(resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ sP1(X1,X0)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ~ sP1(X1,X0) )
          & ( sP1(X1,X0)
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> sP1(X1,X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f62,plain,(
    sP2(sK3) ),
    inference(resolution,[],[f35,f58])).

fof(f58,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f9,f14,f13,f12])).

fof(f13,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ? [X2] :
          ( sP0(X2,X0,X1)
          & ! [X5] :
              ( r1_orders_2(X0,X5,X2)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_0)).

fof(f471,plain,
    ( sP1(sK4,sK3)
    | ~ sP0(sK6,sK3,sK4)
    | ~ r1_lattice3(sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_yellow_0(sK3,sK4) ),
    inference(duplicate_literal_removal,[],[f465])).

fof(f465,plain,
    ( sP1(sK4,sK3)
    | ~ sP0(sK6,sK3,sK4)
    | ~ r1_lattice3(sK3,sK4,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | sP1(sK4,sK3)
    | ~ sP0(sK6,sK3,sK4)
    | r2_yellow_0(sK3,sK4)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(resolution,[],[f456,f67])).

fof(f67,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK3,sK7(X3,sK3,sK6),sK6)
      | sP1(X3,sK3)
      | ~ sP0(sK6,sK3,X3)
      | r2_yellow_0(sK3,sK4)
      | ~ r1_lattice3(sK3,X3,sK6) ) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X2,X1,X0)
      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X2)
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

% (5891)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ sP0(X2,X1,X0)
            | ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X2)
              & r1_lattice3(X1,X0,sK7(X0,X1,X2))
              & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ( sP0(sK8(X0,X1),X1,X0)
          & ! [X5] :
              ( r1_orders_2(X1,X5,sK8(X0,X1))
              | ~ r1_lattice3(X1,X0,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_lattice3(X1,X0,sK8(X0,X1))
          & m1_subset_1(sK8(X0,X1),u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f25,f27,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X2)
          & r1_lattice3(X1,X0,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X2)
        & r1_lattice3(X1,X0,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( sP0(X4,X1,X0)
          & ! [X5] :
              ( r1_orders_2(X1,X5,X4)
              | ~ r1_lattice3(X1,X0,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_lattice3(X1,X0,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP0(sK8(X0,X1),X1,X0)
        & ! [X5] :
            ( r1_orders_2(X1,X5,sK8(X0,X1))
            | ~ r1_lattice3(X1,X0,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & r1_lattice3(X1,X0,sK8(X0,X1))
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ! [X2] :
            ( ~ sP0(X2,X1,X0)
            | ? [X3] :
                ( ~ r1_orders_2(X1,X3,X2)
                & r1_lattice3(X1,X0,X3)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            | ~ r1_lattice3(X1,X0,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP0(X4,X1,X0)
            & ! [X5] :
                ( r1_orders_2(X1,X5,X4)
                | ~ r1_lattice3(X1,X0,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & r1_lattice3(X1,X0,X4)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ! [X2] :
            ( ~ sP0(X2,X0,X1)
            | ? [X5] :
                ( ~ r1_orders_2(X0,X5,X2)
                & r1_lattice3(X0,X1,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP0(X2,X0,X1)
            & ! [X5] :
                ( r1_orders_2(X0,X5,X2)
                | ~ r1_lattice3(X0,X1,X5)
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            & r1_lattice3(X0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f456,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,sK7(sK4,sK3,X0),sK6)
      | sP1(sK4,sK3)
      | ~ sP0(X0,sK3,sK4)
      | ~ r1_lattice3(sK3,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f101,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK3,X0)
      | sP1(X0,sK3) ) ),
    inference(resolution,[],[f62,f42])).

% (5882)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f42,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,sK7(sK4,sK3,X0),sK6)
      | r2_yellow_0(sK3,sK4)
      | sP1(sK4,sK3)
      | ~ sP0(X0,sK3,sK4)
      | ~ r1_lattice3(sK3,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f95,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X2,X1,X0)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X0] :
      ( r1_orders_2(sK3,sK7(sK4,sK3,X0),sK6)
      | ~ m1_subset_1(sK7(sK4,sK3,X0),u1_struct_0(sK3))
      | r2_yellow_0(sK3,sK4)
      | sP1(sK4,sK3)
      | ~ sP0(X0,sK3,sK4)
      | ~ r1_lattice3(sK3,sK4,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f38,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X2,X1,X0)
      | r1_lattice3(X1,X0,sK7(X0,X1,X2))
      | ~ r1_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f701,plain,(
    ~ r2_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f700,f529])).

fof(f529,plain,(
    m1_subset_1(sK8(sK4,sK3),u1_struct_0(sK3)) ),
    inference(resolution,[],[f519,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),u1_struct_0(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f519,plain,(
    sP1(sK4,sK3) ),
    inference(resolution,[],[f476,f105])).

fof(f700,plain,
    ( ~ m1_subset_1(sK8(sK4,sK3),u1_struct_0(sK3))
    | ~ r2_yellow_0(sK3,sK4) ),
    inference(subsumption_resolution,[],[f699,f530])).

fof(f530,plain,(
    r1_lattice3(sK3,sK4,sK8(sK4,sK3)) ),
    inference(resolution,[],[f519,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X1,X0,sK8(X0,X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f699,plain,
    ( ~ r1_lattice3(sK3,sK4,sK8(sK4,sK3))
    | ~ m1_subset_1(sK8(sK4,sK3),u1_struct_0(sK3))
    | ~ r2_yellow_0(sK3,sK4) ),
    inference(resolution,[],[f664,f39])).

fof(f39,plain,(
    ! [X2] :
      ( m1_subset_1(sK5(X2),u1_struct_0(sK3))
      | ~ r1_lattice3(sK3,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ r2_yellow_0(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f664,plain,(
    ~ m1_subset_1(sK5(sK8(sK4,sK3)),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f527,f519])).

fof(f527,plain,
    ( ~ m1_subset_1(sK5(sK8(sK4,sK3)),u1_struct_0(sK3))
    | ~ sP1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f526,f44])).

fof(f526,plain,
    ( ~ m1_subset_1(sK5(sK8(sK4,sK3)),u1_struct_0(sK3))
    | ~ sP1(sK4,sK3)
    | ~ m1_subset_1(sK8(sK4,sK3),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f525,f45])).

fof(f525,plain,
    ( ~ r1_lattice3(sK3,sK4,sK8(sK4,sK3))
    | ~ m1_subset_1(sK5(sK8(sK4,sK3)),u1_struct_0(sK3))
    | ~ sP1(sK4,sK3)
    | ~ m1_subset_1(sK8(sK4,sK3),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f524,f476])).

fof(f524,plain,
    ( ~ r1_lattice3(sK3,sK4,sK8(sK4,sK3))
    | ~ m1_subset_1(sK5(sK8(sK4,sK3)),u1_struct_0(sK3))
    | ~ sP1(sK4,sK3)
    | ~ m1_subset_1(sK8(sK4,sK3),u1_struct_0(sK3))
    | ~ r2_yellow_0(sK3,sK4) ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,
    ( ~ r1_lattice3(sK3,sK4,sK8(sK4,sK3))
    | ~ m1_subset_1(sK5(sK8(sK4,sK3)),u1_struct_0(sK3))
    | ~ sP1(sK4,sK3)
    | ~ r1_lattice3(sK3,sK4,sK8(sK4,sK3))
    | ~ m1_subset_1(sK8(sK4,sK3),u1_struct_0(sK3))
    | ~ r2_yellow_0(sK3,sK4) ),
    inference(resolution,[],[f522,f40])).

fof(f40,plain,(
    ! [X2] :
      ( r1_lattice3(sK3,sK4,sK5(X2))
      | ~ r1_lattice3(sK3,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ r2_yellow_0(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f522,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK3,X0,sK5(sK8(X0,sK3)))
      | ~ r1_lattice3(sK3,sK4,sK8(X0,sK3))
      | ~ m1_subset_1(sK5(sK8(X0,sK3)),u1_struct_0(sK3))
      | ~ sP1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f140,f476])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK3,sK4,sK8(X0,sK3))
      | ~ r2_yellow_0(sK3,sK4)
      | ~ r1_lattice3(sK3,X0,sK5(sK8(X0,sK3)))
      | ~ m1_subset_1(sK5(sK8(X0,sK3)),u1_struct_0(sK3))
      | ~ sP1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK3,sK4,sK8(X0,sK3))
      | ~ m1_subset_1(sK8(X0,sK3),u1_struct_0(sK3))
      | ~ r2_yellow_0(sK3,sK4)
      | ~ r1_lattice3(sK3,X0,sK5(sK8(X0,sK3)))
      | ~ m1_subset_1(sK5(sK8(X0,sK3)),u1_struct_0(sK3))
      | ~ sP1(X0,sK3) ) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X1,X5,sK8(X0,X1))
      | ~ r1_lattice3(X1,X0,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X2] :
      ( ~ r1_orders_2(sK3,sK5(X2),X2)
      | ~ r1_lattice3(sK3,sK4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK3))
      | ~ r2_yellow_0(sK3,sK4) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
