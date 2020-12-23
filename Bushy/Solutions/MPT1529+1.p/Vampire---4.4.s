%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t7_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:48 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 457 expanded)
%              Number of leaves         :   21 ( 178 expanded)
%              Depth                    :   17
%              Number of atoms          :  528 (3605 expanded)
%              Number of equality atoms :   33 ( 138 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f123,f165,f194,f215,f237,f239,f247,f282,f289])).

fof(f289,plain,
    ( spl9_1
    | spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f285,f109])).

fof(f109,plain,
    ( r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_4
  <=> r2_lattice3(sK1,k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f285,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_1
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f284,f94])).

fof(f94,plain,
    ( ~ sP0(sK3,sK2,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_1
  <=> ~ sP0(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f284,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | sP0(sK3,sK2,sK1)
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f283,f100])).

fof(f100,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_3
  <=> ~ r1_orders_2(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f283,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | r1_orders_2(sK1,sK2,sK3)
    | sP0(sK3,sK2,sK1)
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f67,f115])).

fof(f115,plain,
    ( r1_orders_2(sK1,sK3,sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_6
  <=> r1_orders_2(sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f67,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ r1_orders_2(sK1,sK3,sK2)
    | r1_orders_2(sK1,sK2,sK3)
    | sP0(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
        & r1_orders_2(sK1,sK3,sK2) )
      | ( ~ r1_orders_2(sK1,sK3,sK2)
        & r2_lattice3(sK1,k1_tarski(sK3),sK2) )
      | ( ~ r1_lattice3(sK1,k1_tarski(sK3),sK2)
        & r1_orders_2(sK1,sK2,sK3) )
      | sP0(sK3,sK2,sK1) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X2,X1) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & r2_lattice3(X0,k1_tarski(X2),X1) )
                  | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                    & r1_orders_2(X0,X1,X2) )
                  | sP0(X2,X1,X0) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(sK1,k1_tarski(X2),X1)
                  & r1_orders_2(sK1,X2,X1) )
                | ( ~ r1_orders_2(sK1,X2,X1)
                  & r2_lattice3(sK1,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(sK1,k1_tarski(X2),X1)
                  & r1_orders_2(sK1,X1,X2) )
                | sP0(X2,X1,sK1) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X2,X1) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & r2_lattice3(X0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X1,X2) )
                | sP0(X2,X1,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),sK2)
                & r1_orders_2(X0,X2,sK2) )
              | ( ~ r1_orders_2(X0,X2,sK2)
                & r2_lattice3(X0,k1_tarski(X2),sK2) )
              | ( ~ r1_lattice3(X0,k1_tarski(X2),sK2)
                & r1_orders_2(X0,sK2,X2) )
              | sP0(X2,sK2,X0) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
              & r1_orders_2(X0,X2,X1) )
            | ( ~ r1_orders_2(X0,X2,X1)
              & r2_lattice3(X0,k1_tarski(X2),X1) )
            | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
              & r1_orders_2(X0,X1,X2) )
            | sP0(X2,X1,X0) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ( ~ r2_lattice3(X0,k1_tarski(sK3),X1)
            & r1_orders_2(X0,sK3,X1) )
          | ( ~ r1_orders_2(X0,sK3,X1)
            & r2_lattice3(X0,k1_tarski(sK3),X1) )
          | ( ~ r1_lattice3(X0,k1_tarski(sK3),X1)
            & r1_orders_2(X0,X1,sK3) )
          | sP0(sK3,X1,X0) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X2,X1) )
                | ( ~ r1_orders_2(X0,X2,X1)
                  & r2_lattice3(X0,k1_tarski(X2),X1) )
                | ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
                  & r1_orders_2(X0,X1,X2) )
                | sP0(X2,X1,X0) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f21,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ( ~ r1_orders_2(X0,X1,X2)
        & r1_lattice3(X0,k1_tarski(X2),X1) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t7_yellow_0.p',t7_yellow_0)).

fof(f282,plain,
    ( spl9_5
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f280,f58])).

fof(f58,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f280,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f279,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f279,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f278,f106])).

fof(f106,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl9_5
  <=> ~ r2_lattice3(sK1,k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f278,plain,
    ( r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f274,f115])).

fof(f274,plain,
    ( ~ r1_orders_2(sK1,sK3,sK2)
    | r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_5 ),
    inference(superposition,[],[f72,f264])).

fof(f264,plain,
    ( sK3 = sK4(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f252,f90])).

fof(f90,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t7_yellow_0.p',d1_tarski)).

fof(f252,plain,
    ( r2_hidden(sK4(sK1,k1_tarski(sK3),sK2),k1_tarski(sK3))
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f58,f59,f106,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t7_yellow_0.p',d9_lattice3)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f247,plain,
    ( ~ spl9_0
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f134,f97])).

fof(f97,plain,
    ( sP0(sK3,sK2,sK1)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_0
  <=> sP0(sK3,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f134,plain,
    ( ~ sP0(sK3,sK2,sK1)
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f122,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_lattice3(X2,k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_orders_2(X2,X1,X0)
        & r1_lattice3(X2,k1_tarski(X0),X1) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ( ~ r1_orders_2(X0,X1,X2)
        & r1_lattice3(X0,k1_tarski(X2),X1) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f122,plain,
    ( ~ r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl9_9
  <=> ~ r1_lattice3(sK1,k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f239,plain,
    ( ~ spl9_0
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f97,f129])).

fof(f129,plain,
    ( ~ sP0(sK3,sK2,sK1)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f103,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r1_orders_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,
    ( r1_orders_2(sK1,sK2,sK3)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl9_2
  <=> r1_orders_2(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f237,plain,
    ( ~ spl9_4
    | spl9_7 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f221,f59])).

fof(f221,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f58,f89,f112,f60,f109,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f112,plain,
    ( ~ r1_orders_2(sK1,sK3,sK2)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl9_7
  <=> ~ r1_orders_2(sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f89,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f215,plain,
    ( spl9_3
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f198,f60])).

fof(f198,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f58,f89,f119,f59,f100,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t7_yellow_0.p',d8_lattice3)).

fof(f119,plain,
    ( r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl9_8
  <=> r1_lattice3(sK1,k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f194,plain,
    ( ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f192,f58])).

fof(f192,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f191,f59])).

fof(f191,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f190,f169])).

fof(f169,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f168,f119])).

fof(f168,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f166,f115])).

fof(f166,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ r1_orders_2(sK1,sK3,sK2)
    | ~ r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f68,f129])).

fof(f68,plain,
    ( ~ r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ r1_orders_2(sK1,sK3,sK2)
    | ~ r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | sP0(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f190,plain,
    ( r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f186,f115])).

fof(f186,plain,
    ( ~ r1_orders_2(sK1,sK3,sK2)
    | r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(superposition,[],[f72,f176])).

fof(f176,plain,
    ( sK3 = sK4(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f172,f90])).

fof(f172,plain,
    ( r2_hidden(sK4(sK1,k1_tarski(sK3),sK2),k1_tarski(sK3))
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f58,f59,f169,f71])).

fof(f165,plain,
    ( ~ spl9_2
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f163,f58])).

fof(f163,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f162,f59])).

fof(f162,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f161,f122])).

fof(f161,plain,
    ( r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f157,f103])).

fof(f157,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl9_9 ),
    inference(superposition,[],[f76,f145])).

fof(f145,plain,
    ( sK3 = sK5(sK1,k1_tarski(sK3),sK2)
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f144,f90])).

fof(f144,plain,
    ( r2_hidden(sK5(sK1,k1_tarski(sK3),sK2),k1_tarski(sK3))
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f58,f122,f59,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,
    ( spl9_0
    | ~ spl9_9
    | spl9_4
    | spl9_6 ),
    inference(avatar_split_clause,[],[f62,f114,f108,f121,f96])).

fof(f62,plain,
    ( r1_orders_2(sK1,sK3,sK2)
    | r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | ~ r1_lattice3(sK1,k1_tarski(sK3),sK2)
    | sP0(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,
    ( spl9_0
    | spl9_2
    | spl9_4
    | spl9_6 ),
    inference(avatar_split_clause,[],[f61,f114,f108,f102,f96])).

fof(f61,plain,
    ( r1_orders_2(sK1,sK3,sK2)
    | r2_lattice3(sK1,k1_tarski(sK3),sK2)
    | r1_orders_2(sK1,sK2,sK3)
    | sP0(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
