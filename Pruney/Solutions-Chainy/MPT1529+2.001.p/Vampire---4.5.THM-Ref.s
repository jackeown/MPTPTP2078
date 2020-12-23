%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 290 expanded)
%              Number of leaves         :   23 ( 124 expanded)
%              Depth                    :   13
%              Number of atoms          :  561 (1715 expanded)
%              Number of equality atoms :   44 ( 129 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f83,f87,f93,f110,f112,f116,f123,f127,f144,f163,f168,f180,f186,f191])).

fof(f191,plain,
    ( ~ spl6_9
    | spl6_7
    | spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f190,f107,f99,f95,f103])).

fof(f103,plain,
    ( spl6_9
  <=> r2_lattice3(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f95,plain,
    ( spl6_7
  <=> r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f99,plain,
    ( spl6_8
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f107,plain,
    ( spl6_10
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f190,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | spl6_7
    | spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f188,f96])).

fof(f96,plain,
    ( ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f188,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f187,f100])).

fof(f100,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f187,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f42,f109])).

fof(f109,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f42,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
        & r1_orders_2(sK0,sK2,sK1) )
      | ( ~ r1_orders_2(sK0,sK2,sK1)
        & r2_lattice3(sK0,k1_tarski(sK2),sK1) )
      | ( ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( ~ r1_orders_2(sK0,sK1,sK2)
        & r1_lattice3(sK0,k1_tarski(sK2),sK1) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X2,X1) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & r2_lattice3(X0,k1_tarski(X2),X1) )
                  | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X1,X2) )
                  | ( ~ r1_orders_2(X0,X1,X2)
                    & r1_lattice3(X0,k1_tarski(X2),X1) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),X1)
                  & r1_orders_2(sK0,X2,X1) )
                | ( ~ r1_orders_2(sK0,X2,X1)
                  & r2_lattice3(sK0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(sK0,k1_tarski(X2),X1)
                  & r1_orders_2(sK0,X1,X2) )
                | ( ~ r1_orders_2(sK0,X1,X2)
                  & r1_lattice3(sK0,k1_tarski(X2),X1) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),X1)
                & r1_orders_2(sK0,X2,X1) )
              | ( ~ r1_orders_2(sK0,X2,X1)
                & r2_lattice3(sK0,k1_tarski(X2),X1) )
              | ( ~ r1_lattice3(sK0,k1_tarski(X2),X1)
                & r1_orders_2(sK0,X1,X2) )
              | ( ~ r1_orders_2(sK0,X1,X2)
                & r1_lattice3(sK0,k1_tarski(X2),X1) ) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),sK1)
              & r1_orders_2(sK0,X2,sK1) )
            | ( ~ r1_orders_2(sK0,X2,sK1)
              & r2_lattice3(sK0,k1_tarski(X2),sK1) )
            | ( ~ r1_lattice3(sK0,k1_tarski(X2),sK1)
              & r1_orders_2(sK0,sK1,X2) )
            | ( ~ r1_orders_2(sK0,sK1,X2)
              & r1_lattice3(sK0,k1_tarski(X2),sK1) ) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ( ( ~ r2_lattice3(sK0,k1_tarski(X2),sK1)
            & r1_orders_2(sK0,X2,sK1) )
          | ( ~ r1_orders_2(sK0,X2,sK1)
            & r2_lattice3(sK0,k1_tarski(X2),sK1) )
          | ( ~ r1_lattice3(sK0,k1_tarski(X2),sK1)
            & r1_orders_2(sK0,sK1,X2) )
          | ( ~ r1_orders_2(sK0,sK1,X2)
            & r1_lattice3(sK0,k1_tarski(X2),sK1) ) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
          & r1_orders_2(sK0,sK2,sK1) )
        | ( ~ r1_orders_2(sK0,sK2,sK1)
          & r2_lattice3(sK0,k1_tarski(sK2),sK1) )
        | ( ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
          & r1_orders_2(sK0,sK1,sK2) )
        | ( ~ r1_orders_2(sK0,sK1,sK2)
          & r1_lattice3(sK0,k1_tarski(sK2),sK1) ) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X2,X1) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & r2_lattice3(X0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X1,X2) )
                | ( ~ r1_orders_2(X0,X1,X2)
                  & r1_lattice3(X0,k1_tarski(X2),X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                   => r2_lattice3(X0,k1_tarski(X2),X1) )
                  & ( r2_lattice3(X0,k1_tarski(X2),X1)
                   => r1_orders_2(X0,X2,X1) )
                  & ( r1_orders_2(X0,X1,X2)
                   => r1_lattice3(X0,k1_tarski(X2),X1) )
                  & ( r1_lattice3(X0,k1_tarski(X2),X1)
                   => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f186,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | spl6_8 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f64,f59,f97,f69,f74,f100,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
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

fof(f74,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f69,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f97,plain,
    ( r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f59,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f64,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f180,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f178,f64])).

fof(f178,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_2
    | spl6_9
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f177,f69])).

fof(f177,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl6_9
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f176,f104])).

fof(f104,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f176,plain,
    ( r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f174,f109])).

fof(f174,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_14 ),
    inference(superposition,[],[f53,f167])).

fof(f167,plain,
    ( sK2 = sK4(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl6_14
  <=> sK2 = sK4(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f168,plain,
    ( spl6_14
    | ~ spl6_2
    | spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f162,f114,f103,f67,f165])).

fof(f114,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k1_tarski(X1),X0)
        | sK4(sK0,k1_tarski(X1),X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f162,plain,
    ( sK2 = sK4(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_2
    | spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f161,f69])).

fof(f161,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = sK4(sK0,k1_tarski(sK2),sK1)
    | spl6_9
    | ~ spl6_11 ),
    inference(resolution,[],[f104,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,k1_tarski(X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK4(sK0,k1_tarski(X1),X0) = X1 )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f163,plain,
    ( spl6_7
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f160,f120,f99,f67,f62,f95])).

fof(f120,plain,
    ( spl6_12
  <=> sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f160,plain,
    ( r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f159,f64])).

fof(f159,plain,
    ( r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f154,f69])).

fof(f154,plain,
    ( r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f152,f101])).

fof(f101,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f152,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_12 ),
    inference(superposition,[],[f49,f122])).

fof(f122,plain,
    ( sK2 = sK3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f144,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_9
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_9
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f64,f59,f105,f108,f69,f74,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f108,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f105,plain,
    ( r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f127,plain,
    ( ~ spl6_10
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f126,f103,f99,f95,f107])).

fof(f126,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f125,f97])).

fof(f125,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f124,f105])).

fof(f124,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f45,f101])).

fof(f45,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f123,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f118,f95,f91,f67,f120])).

fof(f91,plain,
    ( spl6_6
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k1_tarski(X1),X0)
        | sK3(sK0,k1_tarski(X1),X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f118,plain,
    ( sK2 = sK3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_2
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f117,f69])).

fof(f117,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_6
    | spl6_7 ),
    inference(resolution,[],[f92,f96])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,k1_tarski(X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK3(sK0,k1_tarski(X1),X0) = X1 )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f116,plain,
    ( spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f89,f85,f114])).

fof(f85,plain,
    ( spl6_5
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k1_tarski(X1),X0)
        | sK4(sK0,k1_tarski(X1),X0) = X1 )
    | ~ spl6_5 ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f112,plain,
    ( ~ spl6_7
    | spl6_9
    | spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f111,f99,f107,f103,f95])).

fof(f111,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f33,f101])).

fof(f33,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f110,plain,
    ( spl6_7
    | spl6_8
    | spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f30,f107,f103,f99,f95])).

fof(f30,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f88,f81,f91])).

fof(f81,plain,
    ( spl6_4
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k1_tarski(X1),X0)
        | sK3(sK0,k1_tarski(X1),X0) = X1 )
    | ~ spl6_4 ),
    inference(resolution,[],[f82,f60])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f87,plain,
    ( spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f79,f62,f85])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f64])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,
    ( spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f78,f62,f81])).

fof(f78,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f48,f64])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:02:52 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.50  % (21161)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (21139)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (21145)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (21139)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (21145)Refutation not found, incomplete strategy% (21145)------------------------------
% 0.21/0.50  % (21145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21145)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21145)Memory used [KB]: 1663
% 0.21/0.50  % (21145)Time elapsed: 0.051 s
% 0.21/0.50  % (21145)------------------------------
% 0.21/0.50  % (21145)------------------------------
% 0.21/0.51  % (21144)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f65,f70,f75,f83,f87,f93,f110,f112,f116,f123,f127,f144,f163,f168,f180,f186,f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ~spl6_9 | spl6_7 | spl6_8 | ~spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f190,f107,f99,f95,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl6_9 <=> r2_lattice3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl6_7 <=> r1_lattice3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl6_8 <=> r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl6_10 <=> r1_orders_2(sK0,sK2,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | (spl6_7 | spl6_8 | ~spl6_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f188,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | r1_lattice3(sK0,k1_tarski(sK2),sK1) | (spl6_8 | ~spl6_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f187,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,sK1,sK2) | spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~spl6_10),
% 0.21/0.51    inference(subsumption_resolution,[],[f42,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK1) | ~spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK2,sK1) | r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ((((~r2_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK2,sK1)) | (~r1_orders_2(sK0,sK2,sK1) & r2_lattice3(sK0,k1_tarski(sK2),sK1)) | (~r1_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK1,sK2)) | (~r1_orders_2(sK0,sK1,sK2) & r1_lattice3(sK0,k1_tarski(sK2),sK1))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | (~r1_orders_2(X0,X1,X2) & r1_lattice3(X0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X2,X1)) | (~r1_orders_2(sK0,X2,X1) & r2_lattice3(sK0,k1_tarski(X2),X1)) | (~r1_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X1,X2)) | (~r1_orders_2(sK0,X1,X2) & r1_lattice3(sK0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X2,X1)) | (~r1_orders_2(sK0,X2,X1) & r2_lattice3(sK0,k1_tarski(X2),X1)) | (~r1_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X1,X2)) | (~r1_orders_2(sK0,X1,X2) & r1_lattice3(sK0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,X2,sK1)) | (~r1_orders_2(sK0,X2,sK1) & r2_lattice3(sK0,k1_tarski(X2),sK1)) | (~r1_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,sK1,X2)) | (~r1_orders_2(sK0,sK1,X2) & r1_lattice3(sK0,k1_tarski(X2),sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,X2,sK1)) | (~r1_orders_2(sK0,X2,sK1) & r2_lattice3(sK0,k1_tarski(X2),sK1)) | (~r1_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,sK1,X2)) | (~r1_orders_2(sK0,sK1,X2) & r1_lattice3(sK0,k1_tarski(X2),sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) => (((~r2_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK2,sK1)) | (~r1_orders_2(sK0,sK2,sK1) & r2_lattice3(sK0,k1_tarski(sK2),sK1)) | (~r1_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK1,sK2)) | (~r1_orders_2(sK0,sK1,sK2) & r1_lattice3(sK0,k1_tarski(sK2),sK1))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | (~r1_orders_2(X0,X1,X2) & r1_lattice3(X0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | spl6_8),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f185])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_7 | spl6_8)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f64,f59,f97,f69,f74,f100,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl6_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl6_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.51    inference(equality_resolution,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(rectify,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    l1_orders_2(sK0) | ~spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl6_1 <=> l1_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | spl6_9 | ~spl6_10 | ~spl6_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    $false | (~spl6_1 | ~spl6_2 | spl6_9 | ~spl6_10 | ~spl6_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f178,f64])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | (~spl6_2 | spl6_9 | ~spl6_10 | ~spl6_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f177,f69])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | (spl6_9 | ~spl6_10 | ~spl6_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f176,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | (~spl6_10 | ~spl6_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f174,f109])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl6_14),
% 0.21/0.51    inference(superposition,[],[f53,f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    sK2 = sK4(sK0,k1_tarski(sK2),sK1) | ~spl6_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl6_14 <=> sK2 = sK4(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK4(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    spl6_14 | ~spl6_2 | spl6_9 | ~spl6_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f162,f114,f103,f67,f165])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl6_11 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X1),X0) | sK4(sK0,k1_tarski(X1),X0) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    sK2 = sK4(sK0,k1_tarski(sK2),sK1) | (~spl6_2 | spl6_9 | ~spl6_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f161,f69])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK2 = sK4(sK0,k1_tarski(sK2),sK1) | (spl6_9 | ~spl6_11)),
% 0.21/0.51    inference(resolution,[],[f104,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_lattice3(sK0,k1_tarski(X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK4(sK0,k1_tarski(X1),X0) = X1) ) | ~spl6_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl6_7 | ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f160,f120,f99,f67,f62,f95])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl6_12 <=> sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    r1_lattice3(sK0,k1_tarski(sK2),sK1) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f159,f64])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~l1_orders_2(sK0) | (~spl6_2 | ~spl6_8 | ~spl6_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f154,f69])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | (~spl6_8 | ~spl6_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK1,sK2) | ~spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl6_12),
% 0.21/0.51    inference(superposition,[],[f49,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    sK2 = sK3(sK0,k1_tarski(sK2),sK1) | ~spl6_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f120])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_9 | spl6_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_9 | spl6_10)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f64,f59,f105,f108,f69,f74,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,sK2,sK1) | spl6_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f107])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~spl6_10 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f126,f103,f99,f95,f107])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,sK2,sK1) | (~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f97])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,sK2,sK1) | ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | (~spl6_8 | ~spl6_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f124,f105])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~spl6_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f45,f101])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl6_12 | ~spl6_2 | ~spl6_6 | spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f118,f95,f91,f67,f120])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl6_6 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k1_tarski(X1),X0) | sK3(sK0,k1_tarski(X1),X0) = X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    sK2 = sK3(sK0,k1_tarski(sK2),sK1) | (~spl6_2 | ~spl6_6 | spl6_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f69])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK2 = sK3(sK0,k1_tarski(sK2),sK1) | (~spl6_6 | spl6_7)),
% 0.21/0.51    inference(resolution,[],[f92,f96])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_lattice3(sK0,k1_tarski(X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK3(sK0,k1_tarski(X1),X0) = X1) ) | ~spl6_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl6_11 | ~spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f89,f85,f114])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl6_5 <=> ! [X1,X0] : (r2_hidden(sK4(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_lattice3(sK0,k1_tarski(X1),X0) | sK4(sK0,k1_tarski(X1),X0) = X1) ) | ~spl6_5),
% 0.21/0.51    inference(resolution,[],[f86,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.51    inference(equality_resolution,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~spl6_7 | spl6_9 | spl6_10 | ~spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f111,f99,f107,f103,f95])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~spl6_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f33,f101])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl6_7 | spl6_8 | spl6_9 | spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f107,f103,f99,f95])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k1_tarski(sK2),sK1) | r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k1_tarski(sK2),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl6_6 | ~spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f81,f91])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl6_4 <=> ! [X1,X0] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k1_tarski(X1),X0) | sK3(sK0,k1_tarski(X1),X0) = X1) ) | ~spl6_4),
% 0.21/0.51    inference(resolution,[],[f82,f60])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl6_5 | ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f62,f85])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl6_1),
% 0.21/0.51    inference(resolution,[],[f52,f64])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl6_4 | ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f78,f62,f81])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | ~spl6_1),
% 0.21/0.51    inference(resolution,[],[f48,f64])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f72])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f67])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f62])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    l1_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (21139)------------------------------
% 0.21/0.51  % (21139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21139)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (21139)Memory used [KB]: 6268
% 0.21/0.51  % (21139)Time elapsed: 0.093 s
% 0.21/0.51  % (21139)------------------------------
% 0.21/0.51  % (21139)------------------------------
% 0.21/0.51  % (21135)Success in time 0.15 s
%------------------------------------------------------------------------------
