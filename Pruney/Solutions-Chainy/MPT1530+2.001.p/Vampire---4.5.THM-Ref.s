%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 687 expanded)
%              Number of leaves         :   25 ( 290 expanded)
%              Depth                    :   14
%              Number of atoms          :  741 (6684 expanded)
%              Number of equality atoms :   74 ( 345 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f105,f199,f221,f232,f243,f245,f257,f265,f275,f279,f289,f300,f302])).

fof(f302,plain,
    ( spl9_2
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f77,f131])).

fof(f131,plain,
    ( r1_orders_2(sK2,sK3,sK5)
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X3,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_lattice3(X3,k2_tarski(X2,X1),X0)
        & r1_orders_2(X3,X0,X1)
        & r1_orders_2(X3,X0,X2) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X1,X3)
        & r1_orders_2(X0,X1,X2) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X1,X3)
        & r1_orders_2(X0,X1,X2) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f81,plain,
    ( sP0(sK3,sK5,sK4,sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl9_3
  <=> sP0(sK3,sK5,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f77,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl9_2
  <=> r1_orders_2(sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f300,plain,
    ( ~ spl9_3
    | spl9_7
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl9_3
    | spl9_7
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f298,f43])).

fof(f43,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f22,f21,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
    ( ? [X1] :
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
   => ( ? [X2] :
          ( ? [X3] :
              ( ( sP1(sK3,X3,X2,sK2)
                | ( ( ~ r1_orders_2(sK2,X3,sK3)
                    | ~ r1_orders_2(sK2,X2,sK3) )
                  & r2_lattice3(sK2,k2_tarski(X2,X3),sK3) )
                | sP0(sK3,X3,X2,sK2)
                | ( ( ~ r1_orders_2(sK2,sK3,X3)
                    | ~ r1_orders_2(sK2,sK3,X2) )
                  & r1_lattice3(sK2,k2_tarski(X2,X3),sK3) ) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( sP1(sK3,X3,X2,sK2)
              | ( ( ~ r1_orders_2(sK2,X3,sK3)
                  | ~ r1_orders_2(sK2,X2,sK3) )
                & r2_lattice3(sK2,k2_tarski(X2,X3),sK3) )
              | sP0(sK3,X3,X2,sK2)
              | ( ( ~ r1_orders_2(sK2,sK3,X3)
                  | ~ r1_orders_2(sK2,sK3,X2) )
                & r1_lattice3(sK2,k2_tarski(X2,X3),sK3) ) )
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ? [X3] :
          ( ( sP1(sK3,X3,sK4,sK2)
            | ( ( ~ r1_orders_2(sK2,X3,sK3)
                | ~ r1_orders_2(sK2,sK4,sK3) )
              & r2_lattice3(sK2,k2_tarski(sK4,X3),sK3) )
            | sP0(sK3,X3,sK4,sK2)
            | ( ( ~ r1_orders_2(sK2,sK3,X3)
                | ~ r1_orders_2(sK2,sK3,sK4) )
              & r1_lattice3(sK2,k2_tarski(sK4,X3),sK3) ) )
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ( sP1(sK3,X3,sK4,sK2)
          | ( ( ~ r1_orders_2(sK2,X3,sK3)
              | ~ r1_orders_2(sK2,sK4,sK3) )
            & r2_lattice3(sK2,k2_tarski(sK4,X3),sK3) )
          | sP0(sK3,X3,sK4,sK2)
          | ( ( ~ r1_orders_2(sK2,sK3,X3)
              | ~ r1_orders_2(sK2,sK3,sK4) )
            & r1_lattice3(sK2,k2_tarski(sK4,X3),sK3) ) )
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ( sP1(sK3,sK5,sK4,sK2)
        | ( ( ~ r1_orders_2(sK2,sK5,sK3)
            | ~ r1_orders_2(sK2,sK4,sK3) )
          & r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) )
        | sP0(sK3,sK5,sK4,sK2)
        | ( ( ~ r1_orders_2(sK2,sK3,sK5)
            | ~ r1_orders_2(sK2,sK3,sK4) )
          & r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ) )
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(definition_folding,[],[f7,f13,f12])).

fof(f13,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f298,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl9_3
    | spl9_7
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f297,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f297,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_3
    | spl9_7
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f296,f97])).

fof(f97,plain,
    ( ~ r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_7
  <=> r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f296,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_3
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f295,f130])).

fof(f130,plain,
    ( r1_orders_2(sK2,sK3,sK4)
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f295,plain,
    ( ~ r1_orders_2(sK2,sK3,sK4)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_10 ),
    inference(superposition,[],[f54,f198])).

fof(f198,plain,
    ( sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl9_10
  <=> sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

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

fof(f289,plain,
    ( ~ spl9_3
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f286,f81])).

fof(f286,plain,
    ( ~ sP0(sK3,sK5,sK4,sK2)
    | ~ spl9_7 ),
    inference(resolution,[],[f98,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X3,k2_tarski(X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,
    ( r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f279,plain,
    ( spl9_2
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl9_2
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f229,f77])).

fof(f229,plain,
    ( r1_orders_2(sK2,sK3,sK5)
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f227,f46])).

fof(f46,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f227,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK5)
    | ~ spl9_7 ),
    inference(resolution,[],[f225,f66])).

fof(f66,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK8(X0,X1,X2) != X1
              & sK8(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X1
            | sK8(X0,X1,X2) = X0
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X1
            & sK8(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X1
          | sK8(X0,X1,X2) = X0
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK3,X0) )
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f224,f43])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK3,X0)
        | ~ l1_orders_2(sK2) )
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f223,f44])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2) )
    | ~ spl9_7 ),
    inference(resolution,[],[f98,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f275,plain,
    ( ~ spl9_6
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f272,f93])).

fof(f93,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_6
  <=> sP1(sK3,sK5,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f272,plain,
    ( ~ sP1(sK3,sK5,sK4,sK2)
    | ~ spl9_6
    | ~ spl9_12 ),
    inference(resolution,[],[f271,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X3,k2_tarski(X2,X1),X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r2_lattice3(X3,k2_tarski(X2,X1),X0)
        & r1_orders_2(X3,X1,X0)
        & r1_orders_2(X3,X2,X0) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X1,X3,X2,X0] :
      ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
        & r1_orders_2(X0,X3,X1)
        & r1_orders_2(X0,X2,X1) )
      | ~ sP1(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f271,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_6
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f270,f43])).

fof(f270,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl9_6
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f269,f44])).

fof(f269,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_6
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f268,f202])).

fof(f202,plain,
    ( r1_orders_2(sK2,sK4,sK3)
    | ~ spl9_6 ),
    inference(resolution,[],[f93,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_orders_2(X3,X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f268,plain,
    ( ~ r1_orders_2(sK2,sK4,sK3)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_12 ),
    inference(superposition,[],[f58,f220])).

fof(f220,plain,
    ( sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl9_12
  <=> sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
        & r2_hidden(sK7(X0,X1,X2),X1)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

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

fof(f265,plain,
    ( ~ spl9_6
    | ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f262,f93])).

fof(f262,plain,
    ( ~ sP1(sK3,sK5,sK4,sK2)
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(resolution,[],[f261,f39])).

fof(f261,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f260,f43])).

fof(f260,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f259,f44])).

fof(f259,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_6
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f258,f203])).

fof(f203,plain,
    ( r1_orders_2(sK2,sK5,sK3)
    | ~ spl9_6 ),
    inference(resolution,[],[f93,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_orders_2(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f258,plain,
    ( ~ r1_orders_2(sK2,sK5,sK3)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_11 ),
    inference(superposition,[],[f58,f216])).

fof(f216,plain,
    ( sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl9_11
  <=> sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f257,plain,
    ( spl9_7
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f256,f192,f75,f96])).

fof(f192,plain,
    ( spl9_9
  <=> sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f256,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f255,f43])).

fof(f255,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ l1_orders_2(sK2)
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f254,f44])).

fof(f254,plain,
    ( ~ r1_orders_2(sK2,sK3,sK5)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ spl9_9 ),
    inference(superposition,[],[f54,f194])).

fof(f194,plain,
    ( sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f192])).

fof(f245,plain,
    ( spl9_5
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl9_5
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f240,f89])).

fof(f89,plain,
    ( ~ r1_orders_2(sK2,sK5,sK3)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_5
  <=> r1_orders_2(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f240,plain,
    ( r1_orders_2(sK2,sK5,sK3)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f238,f46])).

fof(f238,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK5,sK3)
    | ~ spl9_8 ),
    inference(resolution,[],[f236,f66])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f235,f43])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3)
        | ~ l1_orders_2(sK2) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f234,f44])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK4,sK5))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2) )
    | ~ spl9_8 ),
    inference(resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,
    ( r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl9_8
  <=> r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f243,plain,
    ( spl9_4
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f241,f85])).

fof(f85,plain,
    ( ~ r1_orders_2(sK2,sK4,sK3)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl9_4
  <=> r1_orders_2(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

% (12596)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f241,plain,
    ( r1_orders_2(sK2,sK4,sK3)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f239,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f239,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK4,sK3)
    | ~ spl9_8 ),
    inference(resolution,[],[f236,f68])).

fof(f68,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f232,plain,
    ( spl9_1
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl9_1
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f230,f73])).

fof(f73,plain,
    ( ~ r1_orders_2(sK2,sK3,sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl9_1
  <=> r1_orders_2(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f230,plain,
    ( r1_orders_2(sK2,sK3,sK4)
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f228,f45])).

fof(f228,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4)
    | ~ spl9_7 ),
    inference(resolution,[],[f225,f68])).

fof(f221,plain,
    ( spl9_11
    | spl9_12
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f212,f91,f218,f214])).

fof(f212,plain,
    ( sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_6 ),
    inference(resolution,[],[f200,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f200,plain,
    ( r2_hidden(sK7(sK2,k2_tarski(sK4,sK5),sK3),k2_tarski(sK4,sK5))
    | ~ spl9_6 ),
    inference(resolution,[],[f93,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ sP1(sK3,X1,X0,sK2)
      | r2_hidden(sK7(sK2,k2_tarski(X0,X1),sK3),k2_tarski(X0,X1)) ) ),
    inference(resolution,[],[f111,f39])).

fof(f111,plain,(
    ! [X1] :
      ( r2_lattice3(sK2,X1,sK3)
      | r2_hidden(sK7(sK2,X1,sK3),X1) ) ),
    inference(subsumption_resolution,[],[f107,f43])).

fof(f107,plain,(
    ! [X1] :
      ( r2_hidden(sK7(sK2,X1,sK3),X1)
      | r2_lattice3(sK2,X1,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f44,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK7(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f199,plain,
    ( spl9_9
    | spl9_10
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f190,f79,f196,f192])).

fof(f190,plain,
    ( sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3)
    | ~ spl9_3 ),
    inference(resolution,[],[f189,f69])).

fof(f189,plain,
    ( r2_hidden(sK6(sK2,k2_tarski(sK4,sK5),sK3),k2_tarski(sK4,sK5))
    | ~ spl9_3 ),
    inference(resolution,[],[f136,f81])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK3,X1,X0,sK2)
      | r2_hidden(sK6(sK2,k2_tarski(X0,X1),sK3),k2_tarski(X0,X1)) ) ),
    inference(resolution,[],[f113,f42])).

fof(f113,plain,(
    ! [X3] :
      ( r1_lattice3(sK2,X3,sK3)
      | r2_hidden(sK6(sK2,X3,sK3),X3) ) ),
    inference(subsumption_resolution,[],[f109,f43])).

fof(f109,plain,(
    ! [X3] :
      ( r2_hidden(sK6(sK2,X3,sK3),X3)
      | r1_lattice3(sK2,X3,sK3)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,
    ( spl9_7
    | spl9_3
    | spl9_8
    | spl9_6 ),
    inference(avatar_split_clause,[],[f47,f91,f101,f79,f96])).

fof(f47,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | spl9_8
    | spl9_6 ),
    inference(avatar_split_clause,[],[f48,f91,f101,f79,f75,f71])).

fof(f48,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f99,plain,
    ( spl9_7
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f49,f91,f87,f83,f79,f96])).

fof(f49,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK5,sK3)
    | ~ r1_orders_2(sK2,sK4,sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f50,f91,f87,f83,f79,f75,f71])).

fof(f50,plain,
    ( sP1(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK5,sK3)
    | ~ r1_orders_2(sK2,sK4,sK3)
    | sP0(sK3,sK5,sK4,sK2)
    | ~ r1_orders_2(sK2,sK3,sK5)
    | ~ r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:55:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (12588)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (12602)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (12585)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (12581)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (12594)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (12583)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (12600)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (12584)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (12601)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (12593)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (12593)Refutation not found, incomplete strategy% (12593)------------------------------
% 0.22/0.52  % (12593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12593)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12593)Memory used [KB]: 6140
% 0.22/0.52  % (12593)Time elapsed: 0.109 s
% 0.22/0.52  % (12593)------------------------------
% 0.22/0.52  % (12593)------------------------------
% 0.22/0.52  % (12586)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (12580)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (12586)Refutation not found, incomplete strategy% (12586)------------------------------
% 0.22/0.52  % (12586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12586)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12586)Memory used [KB]: 10618
% 0.22/0.52  % (12586)Time elapsed: 0.115 s
% 0.22/0.52  % (12586)------------------------------
% 0.22/0.52  % (12586)------------------------------
% 0.22/0.52  % (12599)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (12580)Refutation not found, incomplete strategy% (12580)------------------------------
% 0.22/0.52  % (12580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12580)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12580)Memory used [KB]: 10618
% 0.22/0.52  % (12580)Time elapsed: 0.115 s
% 0.22/0.52  % (12580)------------------------------
% 0.22/0.52  % (12580)------------------------------
% 0.22/0.52  % (12595)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (12587)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (12591)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (12587)Refutation not found, incomplete strategy% (12587)------------------------------
% 0.22/0.53  % (12587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12582)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (12587)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12587)Memory used [KB]: 1663
% 0.22/0.53  % (12587)Time elapsed: 0.120 s
% 0.22/0.53  % (12587)------------------------------
% 0.22/0.53  % (12587)------------------------------
% 0.22/0.53  % (12590)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (12597)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (12581)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f94,f99,f104,f105,f199,f221,f232,f243,f245,f257,f265,f275,f279,f289,f300,f302])).
% 0.22/0.53  fof(f302,plain,(
% 0.22/0.53    spl9_2 | ~spl9_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f301])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    $false | (spl9_2 | ~spl9_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f77,f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK3,sK5) | ~spl9_3),
% 0.22/0.53    inference(resolution,[],[f81,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X3,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((~r1_lattice3(X3,k2_tarski(X2,X1),X0) & r1_orders_2(X3,X0,X1) & r1_orders_2(X3,X0,X2)) | ~sP0(X0,X1,X2,X3))),
% 0.22/0.53    inference(rectify,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X1,X3,X2,X0] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~sP0(X1,X3,X2,X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X1,X3,X2,X0] : ((~r1_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ~sP0(X1,X3,X2,X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    sP0(sK3,sK5,sK4,sK2) | ~spl9_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl9_3 <=> sP0(sK3,sK5,sK4,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK3,sK5) | spl9_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl9_2 <=> r1_orders_2(sK2,sK3,sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    ~spl9_3 | spl9_7 | ~spl9_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f299])).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    $false | (~spl9_3 | spl9_7 | ~spl9_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f298,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    l1_orders_2(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ((((sP1(sK3,sK5,sK4,sK2) | ((~r1_orders_2(sK2,sK5,sK3) | ~r1_orders_2(sK2,sK4,sK3)) & r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)) | sP0(sK3,sK5,sK4,sK2) | ((~r1_orders_2(sK2,sK3,sK5) | ~r1_orders_2(sK2,sK3,sK4)) & r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3))) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f14,f22,f21,f20,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,sK2) | ((~r1_orders_2(sK2,X3,X1) | ~r1_orders_2(sK2,X2,X1)) & r2_lattice3(sK2,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,sK2) | ((~r1_orders_2(sK2,X1,X3) | ~r1_orders_2(sK2,X1,X2)) & r1_lattice3(sK2,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,sK2) | ((~r1_orders_2(sK2,X3,X1) | ~r1_orders_2(sK2,X2,X1)) & r2_lattice3(sK2,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,sK2) | ((~r1_orders_2(sK2,X1,X3) | ~r1_orders_2(sK2,X1,X2)) & r1_lattice3(sK2,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (? [X3] : ((sP1(sK3,X3,X2,sK2) | ((~r1_orders_2(sK2,X3,sK3) | ~r1_orders_2(sK2,X2,sK3)) & r2_lattice3(sK2,k2_tarski(X2,X3),sK3)) | sP0(sK3,X3,X2,sK2) | ((~r1_orders_2(sK2,sK3,X3) | ~r1_orders_2(sK2,sK3,X2)) & r1_lattice3(sK2,k2_tarski(X2,X3),sK3))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X2] : (? [X3] : ((sP1(sK3,X3,X2,sK2) | ((~r1_orders_2(sK2,X3,sK3) | ~r1_orders_2(sK2,X2,sK3)) & r2_lattice3(sK2,k2_tarski(X2,X3),sK3)) | sP0(sK3,X3,X2,sK2) | ((~r1_orders_2(sK2,sK3,X3) | ~r1_orders_2(sK2,sK3,X2)) & r1_lattice3(sK2,k2_tarski(X2,X3),sK3))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) => (? [X3] : ((sP1(sK3,X3,sK4,sK2) | ((~r1_orders_2(sK2,X3,sK3) | ~r1_orders_2(sK2,sK4,sK3)) & r2_lattice3(sK2,k2_tarski(sK4,X3),sK3)) | sP0(sK3,X3,sK4,sK2) | ((~r1_orders_2(sK2,sK3,X3) | ~r1_orders_2(sK2,sK3,sK4)) & r1_lattice3(sK2,k2_tarski(sK4,X3),sK3))) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ? [X3] : ((sP1(sK3,X3,sK4,sK2) | ((~r1_orders_2(sK2,X3,sK3) | ~r1_orders_2(sK2,sK4,sK3)) & r2_lattice3(sK2,k2_tarski(sK4,X3),sK3)) | sP0(sK3,X3,sK4,sK2) | ((~r1_orders_2(sK2,sK3,X3) | ~r1_orders_2(sK2,sK3,sK4)) & r1_lattice3(sK2,k2_tarski(sK4,X3),sK3))) & m1_subset_1(X3,u1_struct_0(sK2))) => ((sP1(sK3,sK5,sK4,sK2) | ((~r1_orders_2(sK2,sK5,sK3) | ~r1_orders_2(sK2,sK4,sK3)) & r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)) | sP0(sK3,sK5,sK4,sK2) | ((~r1_orders_2(sK2,sK3,sK5) | ~r1_orders_2(sK2,sK3,sK4)) & r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3))) & m1_subset_1(sK5,u1_struct_0(sK2)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X1,X3,X2,X0) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | sP0(X1,X3,X2,X0) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.22/0.53    inference(definition_folding,[],[f7,f13,f12])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X1,X3,X2,X0] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~sP1(X1,X3,X2,X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | (~r1_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f6])).
% 0.22/0.53  fof(f6,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) | ((~r1_orders_2(X0,X3,X1) | ~r1_orders_2(X0,X2,X1)) & r2_lattice3(X0,k2_tarski(X2,X3),X1)) | (~r1_lattice3(X0,k2_tarski(X2,X3),X1) & (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))) | ((~r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2)) & r1_lattice3(X0,k2_tarski(X2,X3),X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) => r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r2_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) => r1_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f4])).
% 0.22/0.53  fof(f4,conjecture,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) => r2_lattice3(X0,k2_tarski(X2,X3),X1)) & (r2_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1))) & ((r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2)) => r1_lattice3(X0,k2_tarski(X2,X3),X1)) & (r1_lattice3(X0,k2_tarski(X2,X3),X1) => (r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X1,X2))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    ~l1_orders_2(sK2) | (~spl9_3 | spl9_7 | ~spl9_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f297,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f297,plain,(
% 0.22/0.53    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | (~spl9_3 | spl9_7 | ~spl9_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f296,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    ~r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | spl9_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl9_7 <=> r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.53  fof(f296,plain,(
% 0.22/0.53    r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | (~spl9_3 | ~spl9_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f295,f130])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK3,sK4) | ~spl9_3),
% 0.22/0.53    inference(resolution,[],[f81,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X3,X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK3,sK4) | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~spl9_10),
% 0.22/0.53    inference(superposition,[],[f54,f198])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f196])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    spl9_10 <=> sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(rectify,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    ~spl9_3 | ~spl9_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f288])).
% 0.22/0.53  fof(f288,plain,(
% 0.22/0.53    $false | (~spl9_3 | ~spl9_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f286,f81])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    ~sP0(sK3,sK5,sK4,sK2) | ~spl9_7),
% 0.22/0.53    inference(resolution,[],[f98,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r1_lattice3(X3,k2_tarski(X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f96])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    spl9_2 | ~spl9_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f278])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    $false | (spl9_2 | ~spl9_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f229,f77])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK3,sK5) | ~spl9_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f227,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK5) | ~spl9_7),
% 0.22/0.53    inference(resolution,[],[f225,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.22/0.53    inference(equality_resolution,[],[f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK8(X0,X1,X2) != X1 & sK8(X0,X1,X2) != X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X1 | sK8(X0,X1,X2) = X0 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f34,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X1 & sK8(X0,X1,X2) != X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X1 | sK8(X0,X1,X2) = X0 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(rectify,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,X0)) ) | ~spl9_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f224,f43])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,X0) | ~l1_orders_2(sK2)) ) | ~spl9_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f223,f44])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,X0) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) ) | ~spl9_7),
% 0.22/0.53    inference(resolution,[],[f98,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    ~spl9_6 | ~spl9_12),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f274])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    $false | (~spl9_6 | ~spl9_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f272,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    sP1(sK3,sK5,sK4,sK2) | ~spl9_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl9_6 <=> sP1(sK3,sK5,sK4,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    ~sP1(sK3,sK5,sK4,sK2) | (~spl9_6 | ~spl9_12)),
% 0.22/0.53    inference(resolution,[],[f271,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~r2_lattice3(X3,k2_tarski(X2,X1),X0) | ~sP1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((~r2_lattice3(X3,k2_tarski(X2,X1),X0) & r1_orders_2(X3,X1,X0) & r1_orders_2(X3,X2,X0)) | ~sP1(X0,X1,X2,X3))),
% 0.22/0.53    inference(rectify,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X1,X3,X2,X0] : ((~r2_lattice3(X0,k2_tarski(X2,X3),X1) & r1_orders_2(X0,X3,X1) & r1_orders_2(X0,X2,X1)) | ~sP1(X1,X3,X2,X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f13])).
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | (~spl9_6 | ~spl9_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f270,f43])).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~l1_orders_2(sK2) | (~spl9_6 | ~spl9_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f269,f44])).
% 0.22/0.53  fof(f269,plain,(
% 0.22/0.53    r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | (~spl9_6 | ~spl9_12)),
% 0.22/0.53    inference(subsumption_resolution,[],[f268,f202])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK4,sK3) | ~spl9_6),
% 0.22/0.53    inference(resolution,[],[f93,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_orders_2(X3,X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK4,sK3) | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~spl9_12),
% 0.22/0.53    inference(superposition,[],[f58,f220])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f218])).
% 0.22/0.53  fof(f218,plain,(
% 0.22/0.53    spl9_12 <=> sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK7(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK7(X0,X1,X2),X2) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f29,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK7(X0,X1,X2),X2) & r2_hidden(sK7(X0,X1,X2),X1) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(rectify,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.22/0.53  fof(f265,plain,(
% 0.22/0.53    ~spl9_6 | ~spl9_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f264])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    $false | (~spl9_6 | ~spl9_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f262,f93])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    ~sP1(sK3,sK5,sK4,sK2) | (~spl9_6 | ~spl9_11)),
% 0.22/0.53    inference(resolution,[],[f261,f39])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | (~spl9_6 | ~spl9_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f260,f43])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~l1_orders_2(sK2) | (~spl9_6 | ~spl9_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f259,f44])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | (~spl9_6 | ~spl9_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f258,f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK5,sK3) | ~spl9_6),
% 0.22/0.53    inference(resolution,[],[f93,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_orders_2(X3,X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK5,sK3) | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~spl9_11),
% 0.22/0.53    inference(superposition,[],[f58,f216])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f214])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    spl9_11 <=> sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.53  fof(f257,plain,(
% 0.22/0.53    spl9_7 | ~spl9_2 | ~spl9_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f256,f192,f75,f96])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    spl9_9 <=> sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK3,sK5) | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_9),
% 0.22/0.53    inference(subsumption_resolution,[],[f255,f43])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK3,sK5) | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~l1_orders_2(sK2) | ~spl9_9),
% 0.22/0.53    inference(subsumption_resolution,[],[f254,f44])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK3,sK5) | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~spl9_9),
% 0.22/0.53    inference(superposition,[],[f54,f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f192])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    spl9_5 | ~spl9_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    $false | (spl9_5 | ~spl9_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f240,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK5,sK3) | spl9_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl9_5 <=> r1_orders_2(sK2,sK5,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK5,sK3) | ~spl9_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f238,f46])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK2)) | r1_orders_2(sK2,sK5,sK3) | ~spl9_8),
% 0.22/0.53    inference(resolution,[],[f236,f66])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK3)) ) | ~spl9_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f235,f43])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK3) | ~l1_orders_2(sK2)) ) | ~spl9_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f234,f44])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK4,sK5)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2)) ) | ~spl9_8),
% 0.22/0.53    inference(resolution,[],[f103,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl9_8 <=> r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    spl9_4 | ~spl9_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f242])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    $false | (spl9_4 | ~spl9_8)),
% 0.22/0.53    inference(subsumption_resolution,[],[f241,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK4,sK3) | spl9_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl9_4 <=> r1_orders_2(sK2,sK4,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.53  % (12596)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK4,sK3) | ~spl9_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f239,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK2)) | r1_orders_2(sK2,sK4,sK3) | ~spl9_8),
% 0.22/0.53    inference(resolution,[],[f236,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f232,plain,(
% 0.22/0.53    spl9_1 | ~spl9_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f231])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    $false | (spl9_1 | ~spl9_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f230,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ~r1_orders_2(sK2,sK3,sK4) | spl9_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl9_1 <=> r1_orders_2(sK2,sK3,sK4)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    r1_orders_2(sK2,sK3,sK4) | ~spl9_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f228,f45])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4) | ~spl9_7),
% 0.22/0.53    inference(resolution,[],[f225,f68])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    spl9_11 | spl9_12 | ~spl9_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f212,f91,f218,f214])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    sK4 = sK7(sK2,k2_tarski(sK4,sK5),sK3) | sK5 = sK7(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_6),
% 0.22/0.53    inference(resolution,[],[f200,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.22/0.53    inference(equality_resolution,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    r2_hidden(sK7(sK2,k2_tarski(sK4,sK5),sK3),k2_tarski(sK4,sK5)) | ~spl9_6),
% 0.22/0.53    inference(resolution,[],[f93,f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP1(sK3,X1,X0,sK2) | r2_hidden(sK7(sK2,k2_tarski(X0,X1),sK3),k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(resolution,[],[f111,f39])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ( ! [X1] : (r2_lattice3(sK2,X1,sK3) | r2_hidden(sK7(sK2,X1,sK3),X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f107,f43])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(sK7(sK2,X1,sK3),X1) | r2_lattice3(sK2,X1,sK3) | ~l1_orders_2(sK2)) )),
% 0.22/0.53    inference(resolution,[],[f44,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK7(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    spl9_9 | spl9_10 | ~spl9_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f190,f79,f196,f192])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    sK4 = sK6(sK2,k2_tarski(sK4,sK5),sK3) | sK5 = sK6(sK2,k2_tarski(sK4,sK5),sK3) | ~spl9_3),
% 0.22/0.53    inference(resolution,[],[f189,f69])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    r2_hidden(sK6(sK2,k2_tarski(sK4,sK5),sK3),k2_tarski(sK4,sK5)) | ~spl9_3),
% 0.22/0.53    inference(resolution,[],[f136,f81])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~sP0(sK3,X1,X0,sK2) | r2_hidden(sK6(sK2,k2_tarski(X0,X1),sK3),k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(resolution,[],[f113,f42])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X3] : (r1_lattice3(sK2,X3,sK3) | r2_hidden(sK6(sK2,X3,sK3),X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f43])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(sK6(sK2,X3,sK3),X3) | r1_lattice3(sK2,X3,sK3) | ~l1_orders_2(sK2)) )),
% 0.22/0.53    inference(resolution,[],[f44,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK6(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl9_7 | spl9_3 | spl9_8 | spl9_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f91,f101,f79,f96])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    sP1(sK3,sK5,sK4,sK2) | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | sP0(sK3,sK5,sK4,sK2) | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ~spl9_1 | ~spl9_2 | spl9_3 | spl9_8 | spl9_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f91,f101,f79,f75,f71])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    sP1(sK3,sK5,sK4,sK2) | r2_lattice3(sK2,k2_tarski(sK4,sK5),sK3) | sP0(sK3,sK5,sK4,sK2) | ~r1_orders_2(sK2,sK3,sK5) | ~r1_orders_2(sK2,sK3,sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl9_7 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f91,f87,f83,f79,f96])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    sP1(sK3,sK5,sK4,sK2) | ~r1_orders_2(sK2,sK5,sK3) | ~r1_orders_2(sK2,sK4,sK3) | sP0(sK3,sK5,sK4,sK2) | r1_lattice3(sK2,k2_tarski(sK4,sK5),sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ~spl9_1 | ~spl9_2 | spl9_3 | ~spl9_4 | ~spl9_5 | spl9_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f91,f87,f83,f79,f75,f71])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    sP1(sK3,sK5,sK4,sK2) | ~r1_orders_2(sK2,sK5,sK3) | ~r1_orders_2(sK2,sK4,sK3) | sP0(sK3,sK5,sK4,sK2) | ~r1_orders_2(sK2,sK3,sK5) | ~r1_orders_2(sK2,sK3,sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (12581)------------------------------
% 0.22/0.53  % (12581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12581)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (12581)Memory used [KB]: 10746
% 0.22/0.53  % (12581)Time elapsed: 0.124 s
% 0.22/0.53  % (12581)------------------------------
% 0.22/0.53  % (12581)------------------------------
% 0.22/0.53  % (12579)Success in time 0.172 s
%------------------------------------------------------------------------------
