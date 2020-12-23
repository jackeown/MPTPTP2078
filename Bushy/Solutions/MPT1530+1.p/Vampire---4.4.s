%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t8_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
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

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 694 expanded)
%              Number of leaves         :   27 ( 293 expanded)
%              Depth                    :   14
%              Number of atoms          :  756 (6703 expanded)
%              Number of equality atoms :   74 ( 345 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f727,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f144,f151,f158,f159,f355,f377,f488,f649,f652,f662,f665,f670,f672,f681,f689,f708,f726])).

fof(f726,plain,
    ( ~ spl11_10
    | spl11_15
    | ~ spl11_32 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_15
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f724,f72])).

fof(f72,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( sP1(sK3,sK5,sK4,sK2)
      | ( ( ~ r1_orders_2(sK2,sK5,sK3)
          | ~ r1_orders_2(sK2,sK4,sK3) )
        & r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) )
      | sP0(sK3,sK5,sK4,sK2)
      | ( ( ~ r1_orders_2(sK2,sK3,sK5)
          | ~ r1_orders_2(sK2,sK3,sK4) )
        & r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ) )
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f39,f47,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( sP1(X1,X3,X2,X0)
                      | ( ( ~ r1_orders_2(X0,X3,X1)
                          | ~ r1_orders_2(X0,X2,X1) )
                        & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      | sP0(X1,X3,X2,X0)
                      | ( ( ~ r1_orders_2(X0,X1,X3)
                          | ~ r1_orders_2(X0,X1,X2) )
                        & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X1,X3,X2,sK2)
                    | ( ( ~ r1_orders_2(sK2,X3,X1)
                        | ~ r1_orders_2(sK2,X2,X1) )
                      & r2_lattice3(sK2,k2_tarski(X2,X3),X1) )
                    | sP0(X1,X3,X2,sK2)
                    | ( ( ~ r1_orders_2(sK2,X1,X3)
                        | ~ r1_orders_2(sK2,X1,X2) )
                      & r1_lattice3(sK2,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | sP0(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( sP1(sK3,X3,X2,X0)
                  | ( ( ~ r1_orders_2(X0,X3,sK3)
                      | ~ r1_orders_2(X0,X2,sK3) )
                    & r2_lattice3(X0,k2_tarski(X2,X3),sK3) )
                  | sP0(sK3,X3,X2,X0)
                  | ( ( ~ r1_orders_2(X0,sK3,X3)
                      | ~ r1_orders_2(X0,sK3,X2) )
                    & r1_lattice3(X0,k2_tarski(X2,X3),sK3) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( sP1(X1,X3,X2,X0)
                | ( ( ~ r1_orders_2(X0,X3,X1)
                    | ~ r1_orders_2(X0,X2,X1) )
                  & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                | sP0(X1,X3,X2,X0)
                | ( ( ~ r1_orders_2(X0,X1,X3)
                    | ~ r1_orders_2(X0,X1,X2) )
                  & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( sP1(X1,X3,sK4,X0)
              | ( ( ~ r1_orders_2(X0,X3,X1)
                  | ~ r1_orders_2(X0,sK4,X1) )
                & r2_lattice3(X0,k2_tarski(sK4,X3),X1) )
              | sP0(X1,X3,sK4,X0)
              | ( ( ~ r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X1,sK4) )
                & r1_lattice3(X0,k2_tarski(sK4,X3),X1) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( sP1(X1,X3,X2,X0)
            | ( ( ~ r1_orders_2(X0,X3,X1)
                | ~ r1_orders_2(X0,X2,X1) )
              & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
            | sP0(X1,X3,X2,X0)
            | ( ( ~ r1_orders_2(X0,X1,X3)
                | ~ r1_orders_2(X0,X1,X2) )
              & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( sP1(X1,sK5,X2,X0)
          | ( ( ~ r1_orders_2(X0,sK5,X1)
              | ~ r1_orders_2(X0,X2,X1) )
            & r2_lattice3(X0,k2_tarski(X2,sK5),X1) )
          | sP0(X1,sK5,X2,X0)
          | ( ( ~ r1_orders_2(X0,X1,sK5)
              | ~ r1_orders_2(X0,X1,X2) )
            & r1_lattice3(X0,k2_tarski(X2,sK5),X1) ) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | sP0(X1,X3,X2,X0)
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f25,f38,f37])).

fof(f37,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X1,X3)
        & r1_orders_2(X0,X1,X2) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f38,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
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
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) )
                       => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) ) )
                      & ( ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) )
                       => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',t8_yellow_0)).

fof(f724,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl11_10
    | ~ spl11_15
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f723,f73])).

fof(f73,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f723,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_10
    | ~ spl11_15
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f722,f154])).

fof(f154,plain,
    ( ~ r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl11_15
  <=> ~ r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f722,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_10
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f721,f463])).

fof(f463,plain,
    ( r1_orders_2(sK2,sK4,sK3)
    | ~ spl11_10 ),
    inference(resolution,[],[f143,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_orders_2(X3,X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r2_lattice3(X3,k2_tarski(X2,X1),X0)
        & r1_orders_2(X3,X1,X0)
        & r1_orders_2(X3,X2,X0) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f143,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl11_10
  <=> sP1(sK3,sK5,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f721,plain,
    ( ~ r1_orders_2(sK2,sK4,sK3)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_32 ),
    inference(superposition,[],[f88,f487])).

fof(f487,plain,
    ( sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl11_32
  <=> sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
                & r2_hidden(sK7(X0,X1,X2),X1)
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',d9_lattice3)).

fof(f708,plain,
    ( ~ spl11_10
    | spl11_15
    | ~ spl11_30 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_15
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f706,f72])).

fof(f706,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl11_10
    | ~ spl11_15
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f705,f73])).

fof(f705,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_10
    | ~ spl11_15
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f704,f154])).

fof(f704,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_10
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f703,f464])).

fof(f464,plain,
    ( r1_orders_2(sK2,sK5,sK3)
    | ~ spl11_10 ),
    inference(resolution,[],[f143,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_orders_2(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f703,plain,
    ( ~ r1_orders_2(sK2,sK5,sK3)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_30 ),
    inference(superposition,[],[f88,f481])).

fof(f481,plain,
    ( sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl11_30
  <=> sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f689,plain,
    ( ~ spl11_10
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | ~ spl11_10
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f523,f143])).

fof(f523,plain,
    ( ~ sP1(sK3,sK5,sK4,sK2)
    | ~ spl11_14 ),
    inference(resolution,[],[f157,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X3,k2_tarski(X2,X1),X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f157,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl11_14
  <=> r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f681,plain,
    ( ~ spl11_4
    | ~ spl11_24 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f678,f125])).

fof(f125,plain,
    ( sP0(sK3,sK5,sK4,sK2)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl11_4
  <=> sP0(sK3,sK5,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f678,plain,
    ( ~ sP0(sK3,sK5,sK4,sK2)
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(resolution,[],[f677,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X3,k2_tarski(X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_lattice3(X3,k2_tarski(X2,X1),X0)
        & r1_orders_2(X3,X0,X1)
        & r1_orders_2(X3,X0,X2) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X1,X3)
        & r1_orders_2(X0,X1,X2) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f677,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f676,f72])).

fof(f676,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f675,f73])).

fof(f675,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_4
    | ~ spl11_24 ),
    inference(subsumption_resolution,[],[f674,f209])).

fof(f209,plain,
    ( r1_orders_2(sK2,sK3,sK4)
    | ~ spl11_4 ),
    inference(resolution,[],[f125,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f674,plain,
    ( ~ r1_orders_2(sK2,sK3,sK4)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_24 ),
    inference(superposition,[],[f84,f354])).

fof(f354,plain,
    ( sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl11_24
  <=> sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
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
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',d8_lattice3)).

fof(f672,plain,(
    spl11_27 ),
    inference(avatar_contradiction_clause,[],[f671])).

fof(f671,plain,
    ( $false
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f376,f73])).

fof(f376,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl11_27
  <=> ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f670,plain,
    ( ~ spl11_4
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f669])).

fof(f669,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f565,f125])).

fof(f565,plain,
    ( ~ sP0(sK3,sK5,sK4,sK2)
    | ~ spl11_12 ),
    inference(resolution,[],[f150,f71])).

fof(f150,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl11_12
  <=> r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f665,plain,
    ( spl11_1
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f663,f113])).

fof(f113,plain,
    ( ~ r1_orders_2(sK2,sK3,sK4)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl11_1
  <=> ~ r1_orders_2(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f663,plain,
    ( r1_orders_2(sK2,sK3,sK4)
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f658,f74])).

fof(f74,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f658,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4)
    | ~ spl11_12 ),
    inference(resolution,[],[f656,f106])).

fof(f106,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK9(X0,X1,X2) != X1
              & sK9(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sK9(X0,X1,X2) = X1
            | sK9(X0,X1,X2) = X0
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK9(X0,X1,X2) != X1
            & sK9(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sK9(X0,X1,X2) = X1
          | sK9(X0,X1,X2) = X0
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t8_yellow_0.p',d2_tarski)).

fof(f656,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK3,X0) )
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f655,f72])).

fof(f655,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK3,X0)
        | ~ l1_orders_2(sK2) )
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f654,f73])).

fof(f654,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2) )
    | ~ spl11_12 ),
    inference(resolution,[],[f150,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f662,plain,
    ( spl11_3
    | ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f661])).

fof(f661,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f660,f119])).

fof(f119,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl11_3
  <=> ~ r1_orders_2(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f660,plain,
    ( r1_orders_2(sK2,sK3,sK5)
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f657,f75])).

fof(f75,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f657,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK5)
    | ~ spl11_12 ),
    inference(resolution,[],[f656,f104])).

fof(f104,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f652,plain,
    ( spl11_7
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f650,f131])).

fof(f131,plain,
    ( ~ r1_orders_2(sK2,sK4,sK3)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl11_7
  <=> ~ r1_orders_2(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f650,plain,
    ( r1_orders_2(sK2,sK4,sK3)
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f645,f74])).

fof(f645,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK4,sK3)
    | ~ spl11_14 ),
    inference(resolution,[],[f616,f106])).

fof(f616,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3) )
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f615,f72])).

fof(f615,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3)
        | ~ l1_orders_2(sK2) )
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f614,f73])).

fof(f614,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2) )
    | ~ spl11_14 ),
    inference(resolution,[],[f157,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f649,plain,
    ( spl11_9
    | ~ spl11_14 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f647,f137])).

fof(f137,plain,
    ( ~ r1_orders_2(sK2,sK5,sK3)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl11_9
  <=> ~ r1_orders_2(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f647,plain,
    ( r1_orders_2(sK2,sK5,sK3)
    | ~ spl11_14 ),
    inference(subsumption_resolution,[],[f644,f75])).

fof(f644,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK5,sK3)
    | ~ spl11_14 ),
    inference(resolution,[],[f616,f104])).

fof(f488,plain,
    ( spl11_30
    | spl11_32
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f472,f142,f486,f480])).

fof(f472,plain,
    ( sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_10 ),
    inference(resolution,[],[f462,f107])).

fof(f107,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f462,plain,
    ( r2_hidden(sK7(sK2,k2_tarski(sK4,sK5),sK3),k2_tarski(sK4,sK5))
    | ~ spl11_10 ),
    inference(resolution,[],[f143,f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X1,X0,sK2)
      | r2_hidden(sK7(sK2,k2_tarski(X0,X1),sK3),k2_tarski(X0,X1)) ) ),
    inference(resolution,[],[f166,f68])).

fof(f166,plain,(
    ! [X1] :
      ( r2_lattice3(sK2,X1,sK3)
      | r2_hidden(sK7(sK2,X1,sK3),X1) ) ),
    inference(subsumption_resolution,[],[f161,f72])).

fof(f161,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK2,X1,sK3),X1)
      | r2_lattice3(sK2,X1,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f73,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f377,plain,
    ( ~ spl11_27
    | spl11_12
    | ~ spl11_4
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f360,f347,f124,f149,f375])).

fof(f347,plain,
    ( spl11_22
  <=> sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f360,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl11_4
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f359,f72])).

fof(f359,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_4
    | ~ spl11_22 ),
    inference(subsumption_resolution,[],[f358,f210])).

fof(f210,plain,
    ( r1_orders_2(sK2,sK3,sK5)
    | ~ spl11_4 ),
    inference(resolution,[],[f125,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f358,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl11_22 ),
    inference(superposition,[],[f84,f348])).

fof(f348,plain,
    ( sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f347])).

fof(f355,plain,
    ( spl11_22
    | spl11_24
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f339,f124,f353,f347])).

fof(f339,plain,
    ( sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl11_4 ),
    inference(resolution,[],[f338,f107])).

fof(f338,plain,
    ( r2_hidden(sK6(sK2,k2_tarski(sK4,sK5),sK3),k2_tarski(sK4,sK5))
    | ~ spl11_4 ),
    inference(resolution,[],[f240,f125])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X1,X0,sK2)
      | r2_hidden(sK6(sK2,k2_tarski(X0,X1),sK3),k2_tarski(X0,X1)) ) ),
    inference(resolution,[],[f168,f71])).

fof(f168,plain,(
    ! [X3] :
      ( r1_lattice3(sK2,X3,sK3)
      | r2_hidden(sK6(sK2,X3,sK3),X3) ) ),
    inference(subsumption_resolution,[],[f163,f72])).

fof(f163,plain,(
    ! [X3] :
      ( r2_hidden(sK6(sK2,X3,sK3),X3)
      | r1_lattice3(sK2,X3,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f73,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f159,plain,
    ( spl11_12
    | spl11_4
    | spl11_14
    | spl11_10 ),
    inference(avatar_split_clause,[],[f76,f142,f156,f124,f149])).

fof(f76,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f158,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | spl11_4
    | spl11_14
    | spl11_10 ),
    inference(avatar_split_clause,[],[f77,f142,f156,f124,f118,f112])).

fof(f77,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f151,plain,
    ( spl11_12
    | spl11_4
    | ~ spl11_7
    | ~ spl11_9
    | spl11_10 ),
    inference(avatar_split_clause,[],[f78,f142,f136,f130,f124,f149])).

fof(f78,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK5,sK3)
    | ~ r1_orders_2(sK2,sK4,sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f144,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | spl11_4
    | ~ spl11_7
    | ~ spl11_9
    | spl11_10 ),
    inference(avatar_split_clause,[],[f79,f142,f136,f130,f124,f118,f112])).

fof(f79,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK5,sK3)
    | ~ r1_orders_2(sK2,sK4,sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
