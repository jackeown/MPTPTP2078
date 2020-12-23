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
% DateTime   : Thu Dec  3 13:15:57 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 239 expanded)
%              Number of leaves         :   18 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  508 (1665 expanded)
%              Number of equality atoms :   71 ( 246 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f114,f115,f116,f123,f157,f181,f183,f185])).

fof(f185,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f86,f79,f104,f91,f96,f101,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
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
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f101,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_4
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f96,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f91,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f104,plain,
    ( r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_5
  <=> r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f79,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f86,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f183,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_7
    | spl6_6 ),
    inference(avatar_split_clause,[],[f74,f107,f111,f103,f99])).

fof(f111,plain,
    ( spl6_7
  <=> r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f107,plain,
    ( spl6_6
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f74,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f35,f56,f56])).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13,f12])).

fof(f12,plain,
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

fof(f13,plain,
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

fof(f14,plain,
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

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f181,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f86,f91,f100,f105,f173])).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( r1_lattice3(X3,k2_tarski(X4,X4),X5)
      | ~ r1_orders_2(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(X3,X5,X4)
      | r1_lattice3(X3,k2_tarski(X4,X4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | r1_lattice3(X3,k2_tarski(X4,X4),X5) ) ),
    inference(superposition,[],[f55,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( sK4(X1,k2_tarski(X2,X2),X0) = X2
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r1_lattice3(X1,k2_tarski(X2,X2),X0) ) ),
    inference(equality_resolution,[],[f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X2
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sK4(X0,k2_tarski(X1,X2),X3) = X1
      | r1_lattice3(X0,k2_tarski(X1,X2),X3) ) ),
    inference(equality_factoring,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4(X0,k2_tarski(X1,X2),X3) = X2
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sK4(X0,k2_tarski(X1,X2),X3) = X1
      | r1_lattice3(X0,k2_tarski(X1,X2),X3) ) ),
    inference(resolution,[],[f54,f82])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,
    ( ~ r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f100,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f157,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f86,f91,f108,f113,f142])).

fof(f142,plain,(
    ! [X4,X5,X3] :
      ( r2_lattice3(X3,k2_tarski(X4,X4),X5)
      | ~ r1_orders_2(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(X3,X4,X5)
      | r2_lattice3(X3,k2_tarski(X4,X4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | r2_lattice3(X3,k2_tarski(X4,X4),X5) ) ),
    inference(superposition,[],[f51,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( sK3(X1,k2_tarski(X2,X2),X0) = X2
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_lattice3(X1,k2_tarski(X2,X2),X0) ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X2
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sK3(X0,k2_tarski(X1,X2),X3) = X1
      | r2_lattice3(X0,k2_tarski(X1,X2),X3) ) ),
    inference(equality_factoring,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( sK3(X0,k2_tarski(X1,X2),X3) = X2
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sK3(X0,k2_tarski(X1,X2),X3) = X1
      | r2_lattice3(X0,k2_tarski(X1,X2),X3) ) ),
    inference(resolution,[],[f50,f82])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f9])).

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
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f113,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f108,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f123,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_6
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_6
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f86,f79,f112,f91,f109,f96,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f112,plain,
    ( r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f116,plain,
    ( spl6_5
    | spl6_4
    | spl6_7
    | spl6_6 ),
    inference(avatar_split_clause,[],[f77,f107,f111,f99,f103])).

fof(f77,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) ),
    inference(definition_unfolding,[],[f32,f56,f56])).

fof(f32,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,
    ( spl6_5
    | spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f66,f111,f107,f99,f103])).

fof(f66,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) ),
    inference(definition_unfolding,[],[f44,f56,f56])).

fof(f44,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f114,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f63,f111,f107,f103,f99])).

fof(f63,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f47,f56,f56])).

fof(f47,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k1_tarski(sK2),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f31,f94])).

fof(f31,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f89])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f29,f84])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.14/0.52  % (430)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.14/0.53  % (437)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.54  % (453)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.33/0.55  % (450)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.33/0.55  % (429)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.55  % (453)Refutation not found, incomplete strategy% (453)------------------------------
% 1.33/0.55  % (453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (453)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (453)Memory used [KB]: 10746
% 1.33/0.55  % (453)Time elapsed: 0.136 s
% 1.33/0.55  % (453)------------------------------
% 1.33/0.55  % (453)------------------------------
% 1.33/0.55  % (445)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.55  % (433)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.55  % (425)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.55  % (426)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.55  % (448)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.33/0.56  % (440)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.33/0.56  % (448)Refutation found. Thanks to Tanya!
% 1.33/0.56  % SZS status Theorem for theBenchmark
% 1.33/0.56  % SZS output start Proof for theBenchmark
% 1.33/0.56  fof(f186,plain,(
% 1.33/0.56    $false),
% 1.33/0.56    inference(avatar_sat_refutation,[],[f87,f92,f97,f114,f115,f116,f123,f157,f181,f183,f185])).
% 1.33/0.56  fof(f185,plain,(
% 1.33/0.56    ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f184])).
% 1.33/0.56  fof(f184,plain,(
% 1.33/0.56    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f86,f79,f104,f91,f96,f101,f52])).
% 1.33/0.56  fof(f52,plain,(
% 1.33/0.56    ( ! [X4,X2,X0,X1] : (~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f23])).
% 1.33/0.56  fof(f23,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.33/0.56  fof(f22,plain,(
% 1.33/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f21,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(rectify,[],[f20])).
% 1.33/0.56  fof(f20,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(nnf_transformation,[],[f11])).
% 1.33/0.56  fof(f11,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(flattening,[],[f10])).
% 1.33/0.56  fof(f10,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(ennf_transformation,[],[f3])).
% 1.33/0.56  fof(f3,axiom,(
% 1.33/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 1.33/0.56  fof(f101,plain,(
% 1.33/0.56    ~r1_orders_2(sK0,sK1,sK2) | spl6_4),
% 1.33/0.56    inference(avatar_component_clause,[],[f99])).
% 1.33/0.56  fof(f99,plain,(
% 1.33/0.56    spl6_4 <=> r1_orders_2(sK0,sK1,sK2)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.33/0.56  fof(f96,plain,(
% 1.33/0.56    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_3),
% 1.33/0.56    inference(avatar_component_clause,[],[f94])).
% 1.33/0.56  fof(f94,plain,(
% 1.33/0.56    spl6_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.33/0.56  fof(f91,plain,(
% 1.33/0.56    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_2),
% 1.33/0.56    inference(avatar_component_clause,[],[f89])).
% 1.33/0.56  fof(f89,plain,(
% 1.33/0.56    spl6_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.33/0.56  fof(f104,plain,(
% 1.33/0.56    r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | ~spl6_5),
% 1.33/0.56    inference(avatar_component_clause,[],[f103])).
% 1.33/0.56  fof(f103,plain,(
% 1.33/0.56    spl6_5 <=> r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.33/0.56  fof(f79,plain,(
% 1.33/0.56    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.33/0.56    inference(equality_resolution,[],[f78])).
% 1.33/0.56  fof(f78,plain,(
% 1.33/0.56    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.33/0.56    inference(equality_resolution,[],[f59])).
% 1.33/0.56  fof(f59,plain,(
% 1.33/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.33/0.56    inference(cnf_transformation,[],[f28])).
% 1.33/0.56  fof(f28,plain,(
% 1.33/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.33/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 1.33/0.56  fof(f27,plain,(
% 1.33/0.56    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f26,plain,(
% 1.33/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.33/0.56    inference(rectify,[],[f25])).
% 1.33/0.56  fof(f25,plain,(
% 1.33/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.33/0.56    inference(flattening,[],[f24])).
% 1.33/0.56  fof(f24,plain,(
% 1.33/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.33/0.56    inference(nnf_transformation,[],[f1])).
% 1.33/0.56  fof(f1,axiom,(
% 1.33/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.33/0.56  fof(f86,plain,(
% 1.33/0.56    l1_orders_2(sK0) | ~spl6_1),
% 1.33/0.56    inference(avatar_component_clause,[],[f84])).
% 1.33/0.56  fof(f84,plain,(
% 1.33/0.56    spl6_1 <=> l1_orders_2(sK0)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.33/0.56  fof(f183,plain,(
% 1.33/0.56    ~spl6_4 | ~spl6_5 | spl6_7 | spl6_6),
% 1.33/0.56    inference(avatar_split_clause,[],[f74,f107,f111,f103,f99])).
% 1.33/0.56  fof(f111,plain,(
% 1.33/0.56    spl6_7 <=> r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.33/0.56  fof(f107,plain,(
% 1.33/0.56    spl6_6 <=> r1_orders_2(sK0,sK2,sK1)),
% 1.33/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.33/0.56  fof(f74,plain,(
% 1.33/0.56    r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | ~r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | ~r1_orders_2(sK0,sK1,sK2)),
% 1.33/0.56    inference(definition_unfolding,[],[f35,f56,f56])).
% 1.33/0.56  fof(f56,plain,(
% 1.33/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f2])).
% 1.33/0.56  fof(f2,axiom,(
% 1.33/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.33/0.56  fof(f35,plain,(
% 1.33/0.56    r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK1,sK2)),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  fof(f15,plain,(
% 1.33/0.56    ((((~r2_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK2,sK1)) | (~r1_orders_2(sK0,sK2,sK1) & r2_lattice3(sK0,k1_tarski(sK2),sK1)) | (~r1_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK1,sK2)) | (~r1_orders_2(sK0,sK1,sK2) & r1_lattice3(sK0,k1_tarski(sK2),sK1))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0)),
% 1.33/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13,f12])).
% 1.33/0.56  fof(f12,plain,(
% 1.33/0.56    ? [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | (~r1_orders_2(X0,X1,X2) & r1_lattice3(X0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X2,X1)) | (~r1_orders_2(sK0,X2,X1) & r2_lattice3(sK0,k1_tarski(X2),X1)) | (~r1_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X1,X2)) | (~r1_orders_2(sK0,X1,X2) & r1_lattice3(sK0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f13,plain,(
% 1.33/0.56    ? [X1] : (? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X2,X1)) | (~r1_orders_2(sK0,X2,X1) & r2_lattice3(sK0,k1_tarski(X2),X1)) | (~r1_lattice3(sK0,k1_tarski(X2),X1) & r1_orders_2(sK0,X1,X2)) | (~r1_orders_2(sK0,X1,X2) & r1_lattice3(sK0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,X2,sK1)) | (~r1_orders_2(sK0,X2,sK1) & r2_lattice3(sK0,k1_tarski(X2),sK1)) | (~r1_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,sK1,X2)) | (~r1_orders_2(sK0,sK1,X2) & r1_lattice3(sK0,k1_tarski(X2),sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f14,plain,(
% 1.33/0.56    ? [X2] : (((~r2_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,X2,sK1)) | (~r1_orders_2(sK0,X2,sK1) & r2_lattice3(sK0,k1_tarski(X2),sK1)) | (~r1_lattice3(sK0,k1_tarski(X2),sK1) & r1_orders_2(sK0,sK1,X2)) | (~r1_orders_2(sK0,sK1,X2) & r1_lattice3(sK0,k1_tarski(X2),sK1))) & m1_subset_1(X2,u1_struct_0(sK0))) => (((~r2_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK2,sK1)) | (~r1_orders_2(sK0,sK2,sK1) & r2_lattice3(sK0,k1_tarski(sK2),sK1)) | (~r1_lattice3(sK0,k1_tarski(sK2),sK1) & r1_orders_2(sK0,sK1,sK2)) | (~r1_orders_2(sK0,sK1,sK2) & r1_lattice3(sK0,k1_tarski(sK2),sK1))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f7,plain,(
% 1.33/0.56    ? [X0] : (? [X1] : (? [X2] : (((~r2_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X2,X1)) | (~r1_orders_2(X0,X2,X1) & r2_lattice3(X0,k1_tarski(X2),X1)) | (~r1_lattice3(X0,k1_tarski(X2),X1) & r1_orders_2(X0,X1,X2)) | (~r1_orders_2(X0,X1,X2) & r1_lattice3(X0,k1_tarski(X2),X1))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 1.33/0.56    inference(ennf_transformation,[],[f6])).
% 1.33/0.56  fof(f6,negated_conjecture,(
% 1.33/0.56    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 1.33/0.56    inference(negated_conjecture,[],[f5])).
% 1.33/0.56  fof(f5,conjecture,(
% 1.33/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 1.33/0.56  fof(f181,plain,(
% 1.33/0.56    ~spl6_1 | ~spl6_2 | ~spl6_4 | spl6_5),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f177])).
% 1.33/0.56  fof(f177,plain,(
% 1.33/0.56    $false | (~spl6_1 | ~spl6_2 | ~spl6_4 | spl6_5)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f86,f91,f100,f105,f173])).
% 1.33/0.56  fof(f173,plain,(
% 1.33/0.56    ( ! [X4,X5,X3] : (r1_lattice3(X3,k2_tarski(X4,X4),X5) | ~r1_orders_2(X3,X5,X4) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3)) )),
% 1.33/0.56    inference(duplicate_literal_removal,[],[f168])).
% 1.33/0.56  fof(f168,plain,(
% 1.33/0.56    ( ! [X4,X5,X3] : (~r1_orders_2(X3,X5,X4) | r1_lattice3(X3,k2_tarski(X4,X4),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~l1_orders_2(X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | r1_lattice3(X3,k2_tarski(X4,X4),X5)) )),
% 1.33/0.56    inference(superposition,[],[f55,f158])).
% 1.33/0.56  fof(f158,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (sK4(X1,k2_tarski(X2,X2),X0) = X2 | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | r1_lattice3(X1,k2_tarski(X2,X2),X0)) )),
% 1.33/0.56    inference(equality_resolution,[],[f149])).
% 1.33/0.56  fof(f149,plain,(
% 1.33/0.56    ( ! [X2,X0,X3,X1] : (X1 != X2 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | sK4(X0,k2_tarski(X1,X2),X3) = X1 | r1_lattice3(X0,k2_tarski(X1,X2),X3)) )),
% 1.33/0.56    inference(equality_factoring,[],[f120])).
% 1.33/0.56  fof(f120,plain,(
% 1.33/0.56    ( ! [X2,X0,X3,X1] : (sK4(X0,k2_tarski(X1,X2),X3) = X2 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | sK4(X0,k2_tarski(X1,X2),X3) = X1 | r1_lattice3(X0,k2_tarski(X1,X2),X3)) )),
% 1.33/0.56    inference(resolution,[],[f54,f82])).
% 1.33/0.56  fof(f82,plain,(
% 1.33/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.33/0.56    inference(equality_resolution,[],[f57])).
% 1.33/0.56  fof(f57,plain,(
% 1.33/0.56    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.33/0.56    inference(cnf_transformation,[],[f28])).
% 1.33/0.56  fof(f54,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f23])).
% 1.33/0.56  fof(f55,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f23])).
% 1.33/0.56  fof(f105,plain,(
% 1.33/0.56    ~r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | spl6_5),
% 1.33/0.56    inference(avatar_component_clause,[],[f103])).
% 1.33/0.56  fof(f100,plain,(
% 1.33/0.56    r1_orders_2(sK0,sK1,sK2) | ~spl6_4),
% 1.33/0.56    inference(avatar_component_clause,[],[f99])).
% 1.33/0.56  fof(f157,plain,(
% 1.33/0.56    ~spl6_1 | ~spl6_2 | ~spl6_6 | spl6_7),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f153])).
% 1.33/0.56  fof(f153,plain,(
% 1.33/0.56    $false | (~spl6_1 | ~spl6_2 | ~spl6_6 | spl6_7)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f86,f91,f108,f113,f142])).
% 1.33/0.56  fof(f142,plain,(
% 1.33/0.56    ( ! [X4,X5,X3] : (r2_lattice3(X3,k2_tarski(X4,X4),X5) | ~r1_orders_2(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3)) )),
% 1.33/0.56    inference(duplicate_literal_removal,[],[f137])).
% 1.33/0.56  fof(f137,plain,(
% 1.33/0.56    ( ! [X4,X5,X3] : (~r1_orders_2(X3,X4,X5) | r2_lattice3(X3,k2_tarski(X4,X4),X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~l1_orders_2(X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | r2_lattice3(X3,k2_tarski(X4,X4),X5)) )),
% 1.33/0.56    inference(superposition,[],[f51,f136])).
% 1.33/0.56  fof(f136,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (sK3(X1,k2_tarski(X2,X2),X0) = X2 | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | r2_lattice3(X1,k2_tarski(X2,X2),X0)) )),
% 1.33/0.56    inference(equality_resolution,[],[f132])).
% 1.33/0.56  fof(f132,plain,(
% 1.33/0.56    ( ! [X2,X0,X3,X1] : (X1 != X2 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | sK3(X0,k2_tarski(X1,X2),X3) = X1 | r2_lattice3(X0,k2_tarski(X1,X2),X3)) )),
% 1.33/0.56    inference(equality_factoring,[],[f119])).
% 1.33/0.56  fof(f119,plain,(
% 1.33/0.56    ( ! [X2,X0,X3,X1] : (sK3(X0,k2_tarski(X1,X2),X3) = X2 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | sK3(X0,k2_tarski(X1,X2),X3) = X1 | r2_lattice3(X0,k2_tarski(X1,X2),X3)) )),
% 1.33/0.56    inference(resolution,[],[f50,f82])).
% 1.33/0.56  fof(f50,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f19])).
% 1.33/0.56  fof(f19,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 1.33/0.56  fof(f18,plain,(
% 1.33/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 1.33/0.56    introduced(choice_axiom,[])).
% 1.33/0.56  fof(f17,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(rectify,[],[f16])).
% 1.33/0.56  fof(f16,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(nnf_transformation,[],[f9])).
% 1.33/0.56  fof(f9,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(flattening,[],[f8])).
% 1.33/0.56  fof(f8,plain,(
% 1.33/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.33/0.56    inference(ennf_transformation,[],[f4])).
% 1.33/0.56  fof(f4,axiom,(
% 1.33/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.33/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 1.33/0.56  fof(f51,plain,(
% 1.33/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f19])).
% 1.33/0.56  fof(f113,plain,(
% 1.33/0.56    ~r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | spl6_7),
% 1.33/0.56    inference(avatar_component_clause,[],[f111])).
% 1.33/0.56  fof(f108,plain,(
% 1.33/0.56    r1_orders_2(sK0,sK2,sK1) | ~spl6_6),
% 1.33/0.56    inference(avatar_component_clause,[],[f107])).
% 1.33/0.56  fof(f123,plain,(
% 1.33/0.56    ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_6 | ~spl6_7),
% 1.33/0.56    inference(avatar_contradiction_clause,[],[f121])).
% 1.33/0.56  fof(f121,plain,(
% 1.33/0.56    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_6 | ~spl6_7)),
% 1.33/0.56    inference(unit_resulting_resolution,[],[f86,f79,f112,f91,f109,f96,f48])).
% 1.33/0.56  fof(f48,plain,(
% 1.33/0.56    ( ! [X4,X2,X0,X1] : (~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.33/0.56    inference(cnf_transformation,[],[f19])).
% 1.33/0.56  fof(f109,plain,(
% 1.33/0.56    ~r1_orders_2(sK0,sK2,sK1) | spl6_6),
% 1.33/0.56    inference(avatar_component_clause,[],[f107])).
% 1.33/0.56  fof(f112,plain,(
% 1.33/0.56    r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | ~spl6_7),
% 1.33/0.56    inference(avatar_component_clause,[],[f111])).
% 1.33/0.56  fof(f116,plain,(
% 1.33/0.56    spl6_5 | spl6_4 | spl6_7 | spl6_6),
% 1.33/0.56    inference(avatar_split_clause,[],[f77,f107,f111,f99,f103])).
% 1.33/0.56  fof(f77,plain,(
% 1.33/0.56    r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)),
% 1.33/0.56    inference(definition_unfolding,[],[f32,f56,f56])).
% 1.33/0.56  fof(f32,plain,(
% 1.33/0.56    r1_orders_2(sK0,sK2,sK1) | r2_lattice3(sK0,k1_tarski(sK2),sK1) | r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k1_tarski(sK2),sK1)),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  fof(f115,plain,(
% 1.33/0.56    spl6_5 | spl6_4 | ~spl6_6 | ~spl6_7),
% 1.33/0.56    inference(avatar_split_clause,[],[f66,f111,f107,f99,f103])).
% 1.33/0.56  fof(f66,plain,(
% 1.33/0.56    ~r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | ~r1_orders_2(sK0,sK2,sK1) | r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1)),
% 1.33/0.56    inference(definition_unfolding,[],[f44,f56,f56])).
% 1.33/0.56  fof(f44,plain,(
% 1.33/0.56    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK2,sK1) | r1_orders_2(sK0,sK1,sK2) | r1_lattice3(sK0,k1_tarski(sK2),sK1)),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  fof(f114,plain,(
% 1.33/0.56    ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7),
% 1.33/0.56    inference(avatar_split_clause,[],[f63,f111,f107,f103,f99])).
% 1.33/0.56  fof(f63,plain,(
% 1.33/0.56    ~r2_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_lattice3(sK0,k2_tarski(sK2,sK2),sK1) | ~r1_orders_2(sK0,sK1,sK2)),
% 1.33/0.56    inference(definition_unfolding,[],[f47,f56,f56])).
% 1.33/0.56  fof(f47,plain,(
% 1.33/0.56    ~r2_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK2,sK1) | ~r1_lattice3(sK0,k1_tarski(sK2),sK1) | ~r1_orders_2(sK0,sK1,sK2)),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  fof(f97,plain,(
% 1.33/0.56    spl6_3),
% 1.33/0.56    inference(avatar_split_clause,[],[f31,f94])).
% 1.33/0.56  fof(f31,plain,(
% 1.33/0.56    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  fof(f92,plain,(
% 1.33/0.56    spl6_2),
% 1.33/0.56    inference(avatar_split_clause,[],[f30,f89])).
% 1.33/0.56  fof(f30,plain,(
% 1.33/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  fof(f87,plain,(
% 1.33/0.56    spl6_1),
% 1.33/0.56    inference(avatar_split_clause,[],[f29,f84])).
% 1.33/0.56  fof(f29,plain,(
% 1.33/0.56    l1_orders_2(sK0)),
% 1.33/0.56    inference(cnf_transformation,[],[f15])).
% 1.33/0.56  % SZS output end Proof for theBenchmark
% 1.33/0.56  % (448)------------------------------
% 1.33/0.56  % (448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (448)Termination reason: Refutation
% 1.33/0.56  
% 1.33/0.56  % (448)Memory used [KB]: 10874
% 1.33/0.56  % (448)Time elapsed: 0.099 s
% 1.33/0.56  % (448)------------------------------
% 1.33/0.56  % (448)------------------------------
% 1.33/0.56  % (426)Refutation not found, incomplete strategy% (426)------------------------------
% 1.33/0.56  % (426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (420)Success in time 0.201 s
%------------------------------------------------------------------------------
