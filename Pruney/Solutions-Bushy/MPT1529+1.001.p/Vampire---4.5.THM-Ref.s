%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1529+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.39s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

% (4543)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
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

% (4558)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (4542)Termination reason: Refutation not found, incomplete strategy

% (4542)Memory used [KB]: 10618
% (4542)Time elapsed: 0.106 s
% (4542)------------------------------
% (4542)------------------------------
% (4561)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

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
