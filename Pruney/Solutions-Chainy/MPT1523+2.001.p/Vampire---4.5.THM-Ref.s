%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 (1046 expanded)
%              Number of leaves         :   20 ( 473 expanded)
%              Depth                    :   36
%              Number of atoms          :  659 (10208 expanded)
%              Number of equality atoms :  104 (2439 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f271,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f89,f92,f193,f210,f219,f246,f270])).

fof(f270,plain,
    ( ~ spl9_1
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f268,f247])).

fof(f247,plain,
    ( r1_orders_2(sK3,sK5,sK5)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f199,f218])).

fof(f218,plain,
    ( sK5 = sK6
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl9_6
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f199,plain,
    ( r1_orders_2(sK3,sK5,sK6)
    | ~ spl9_1 ),
    inference(resolution,[],[f197,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | r1_orders_2(X5,X4,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r1_orders_2(X2,X1,X0)
        & r1_orders_2(X5,X4,X3) )
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X5,X4,X1,X3,X2,X0] :
      ( ( ~ r1_orders_2(X1,X4,X5)
        & r1_orders_2(X0,X2,X3) )
      | ~ sP0(X5,X4,X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X5,X4,X1,X3,X2,X0] :
      ( ( ~ r1_orders_2(X1,X4,X5)
        & r1_orders_2(X0,X2,X3) )
      | ~ sP0(X5,X4,X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f197,plain,
    ( sP0(sK6,sK5,sK4,sK6,sK5,sK3)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f195,f42])).

fof(f42,plain,(
    sK6 = sK8 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ( ~ r2_orders_2(sK4,sK7,sK8)
        & r2_orders_2(sK3,sK5,sK6) )
      | sP0(sK8,sK7,sK4,sK6,sK5,sK3) )
    & sK6 = sK8
    & sK5 = sK7
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK4))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
    & l1_orders_2(sK4)
    & l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f25,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ( ~ r2_orders_2(X1,X4,X5)
                                & r2_orders_2(X0,X2,X3) )
                              | sP0(X5,X4,X1,X3,X2,X0) )
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(sK3,X2,X3) )
                            | sP0(X5,X4,X1,X3,X2,sK3) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK3)) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
          & l1_orders_2(X1) )
      & l1_orders_2(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ( ~ r2_orders_2(X1,X4,X5)
                            & r2_orders_2(sK3,X2,X3) )
                          | sP0(X5,X4,X1,X3,X2,sK3) )
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(sK3)) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ( ~ r2_orders_2(sK4,X4,X5)
                          & r2_orders_2(sK3,X2,X3) )
                        | sP0(X5,X4,sK4,X3,X2,sK3) )
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(sK4)) )
                  & m1_subset_1(X4,u1_struct_0(sK4)) )
              & m1_subset_1(X3,u1_struct_0(sK3)) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))
      & l1_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ( ~ r2_orders_2(sK4,X4,X5)
                        & r2_orders_2(sK3,X2,X3) )
                      | sP0(X5,X4,sK4,X3,X2,sK3) )
                    & X3 = X5
                    & X2 = X4
                    & m1_subset_1(X5,u1_struct_0(sK4)) )
                & m1_subset_1(X4,u1_struct_0(sK4)) )
            & m1_subset_1(X3,u1_struct_0(sK3)) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ( ~ r2_orders_2(sK4,X4,X5)
                      & r2_orders_2(sK3,sK5,X3) )
                    | sP0(X5,X4,sK4,X3,sK5,sK3) )
                  & X3 = X5
                  & sK5 = X4
                  & m1_subset_1(X5,u1_struct_0(sK4)) )
              & m1_subset_1(X4,u1_struct_0(sK4)) )
          & m1_subset_1(X3,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ( ~ r2_orders_2(sK4,X4,X5)
                    & r2_orders_2(sK3,sK5,X3) )
                  | sP0(X5,X4,sK4,X3,sK5,sK3) )
                & X3 = X5
                & sK5 = X4
                & m1_subset_1(X5,u1_struct_0(sK4)) )
            & m1_subset_1(X4,u1_struct_0(sK4)) )
        & m1_subset_1(X3,u1_struct_0(sK3)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ( ~ r2_orders_2(sK4,X4,X5)
                  & r2_orders_2(sK3,sK5,sK6) )
                | sP0(X5,X4,sK4,sK6,sK5,sK3) )
              & sK6 = X5
              & sK5 = X4
              & m1_subset_1(X5,u1_struct_0(sK4)) )
          & m1_subset_1(X4,u1_struct_0(sK4)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ( ~ r2_orders_2(sK4,X4,X5)
                & r2_orders_2(sK3,sK5,sK6) )
              | sP0(X5,X4,sK4,sK6,sK5,sK3) )
            & sK6 = X5
            & sK5 = X4
            & m1_subset_1(X5,u1_struct_0(sK4)) )
        & m1_subset_1(X4,u1_struct_0(sK4)) )
   => ( ? [X5] :
          ( ( ( ~ r2_orders_2(sK4,sK7,X5)
              & r2_orders_2(sK3,sK5,sK6) )
            | sP0(X5,sK7,sK4,sK6,sK5,sK3) )
          & sK6 = X5
          & sK5 = sK7
          & m1_subset_1(X5,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X5] :
        ( ( ( ~ r2_orders_2(sK4,sK7,X5)
            & r2_orders_2(sK3,sK5,sK6) )
          | sP0(X5,sK7,sK4,sK6,sK5,sK3) )
        & sK6 = X5
        & sK5 = sK7
        & m1_subset_1(X5,u1_struct_0(sK4)) )
   => ( ( ( ~ r2_orders_2(sK4,sK7,sK8)
          & r2_orders_2(sK3,sK5,sK6) )
        | sP0(sK8,sK7,sK4,sK6,sK5,sK3) )
      & sK6 = sK8
      & sK5 = sK7
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | sP0(X5,X4,X1,X3,X2,X0) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f13])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f195,plain,
    ( sP0(sK8,sK5,sK4,sK6,sK5,sK3)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f60,f41])).

fof(f41,plain,(
    sK5 = sK7 ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,
    ( sP0(sK8,sK7,sK4,sK6,sK5,sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl9_1
  <=> sP0(sK8,sK7,sK4,sK6,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f268,plain,
    ( ~ r1_orders_2(sK3,sK5,sK5)
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f267,f37])).

fof(f37,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f267,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK5,sK5)
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r1_orders_2(sK3,sK5,sK5)
    | ~ spl9_1
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f249,f138])).

fof(f138,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK4,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f136,f34])).

fof(f34,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f136,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | r1_orders_2(sK4,X3,X2)
        | ~ r1_orders_2(sK3,X3,X2)
        | ~ l1_orders_2(sK3) )
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | r1_orders_2(sK4,X3,X2)
        | ~ r1_orders_2(sK3,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3) )
    | ~ spl9_5 ),
    inference(resolution,[],[f133,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_orders_2(sK4,X0,X1) )
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f132,f94])).

fof(f94,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK4)
    | ~ spl9_5 ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_struct_0(sK4) = X0 )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_5
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_struct_0(sK4) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
        | r1_orders_2(sK4,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f131,f94])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
        | r1_orders_2(sK4,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK4)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f35,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3))
        | r1_orders_2(sK4,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ l1_orders_2(sK4) )
    | ~ spl9_5 ),
    inference(superposition,[],[f53,f113])).

fof(f113,plain,
    ( u1_orders_2(sK3) = u1_orders_2(sK4)
    | ~ spl9_5 ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_orders_2(sK4) = X1 )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f108,f101])).

fof(f101,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ l1_orders_2(sK4)
    | ~ spl9_5 ),
    inference(superposition,[],[f45,f94])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f108,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
        | u1_orders_2(sK4) = X1
        | ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) )
    | ~ spl9_5 ),
    inference(superposition,[],[f55,f97])).

fof(f97,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4))
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f36,f94])).

fof(f36,plain,(
    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f249,plain,
    ( ~ r1_orders_2(sK4,sK5,sK5)
    | ~ spl9_1
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f198,f218])).

fof(f198,plain,
    ( ~ r1_orders_2(sK4,sK5,sK6)
    | ~ spl9_1 ),
    inference(resolution,[],[f197,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | ~ r1_orders_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f246,plain,
    ( spl9_6
    | ~ spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f245,f67,f58,f216])).

fof(f67,plain,
    ( spl9_3
  <=> r2_orders_2(sK3,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f245,plain,
    ( sK5 = sK6
    | ~ spl9_1
    | spl9_3 ),
    inference(subsumption_resolution,[],[f244,f37])).

fof(f244,plain,
    ( sK5 = sK6
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_3 ),
    inference(subsumption_resolution,[],[f243,f68])).

fof(f68,plain,
    ( ~ r2_orders_2(sK3,sK5,sK6)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f243,plain,
    ( r2_orders_2(sK3,sK5,sK6)
    | sK5 = sK6
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f242,f38])).

fof(f38,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f242,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_orders_2(sK3,sK5,sK6)
    | sK5 = sK6
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f234,f34])).

fof(f234,plain,
    ( ~ l1_orders_2(sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | r2_orders_2(sK3,sK5,sK6)
    | sK5 = sK6
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_1 ),
    inference(resolution,[],[f199,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X0,X2)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r2_orders_2(X1,X0,X2)
      | X0 = X2
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f77,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | X0 = X1
      | ~ r1_orders_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | X0 = X1
        | ~ r1_orders_2(X2,X1,X0) )
      & ( ( X0 != X1
          & r1_orders_2(X2,X1,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( sP1(X2,X1,X0)
    <=> ( X1 != X2
        & r1_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_orders_2(X1,X2,X0) ) ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_orders_2(X0,X1,X2)
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r2_orders_2(X0,X1,X2) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_orders_2(X0,X1,X2)
      <=> sP1(X2,X1,X0) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f10,f16,f15])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f219,plain,
    ( ~ spl9_3
    | spl9_6
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f182,f87,f62,f216,f67])).

fof(f62,plain,
    ( spl9_2
  <=> r2_orders_2(sK4,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f182,plain,
    ( sK5 = sK6
    | ~ r2_orders_2(sK3,sK5,sK6)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f181,f37])).

% (28470)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f181,plain,
    ( sK5 = sK6
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_orders_2(sK3,sK5,sK6)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f178,f38])).

fof(f178,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | sK5 = sK6
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ r2_orders_2(sK3,sK5,sK6)
    | spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f168,f74])).

fof(f74,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl9_2 ),
    inference(forward_demodulation,[],[f73,f41])).

fof(f73,plain,
    ( ~ r2_orders_2(sK4,sK7,sK6)
    | spl9_2 ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f64,plain,
    ( ~ r2_orders_2(sK4,sK7,sK8)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f168,plain,
    ( ! [X2,X3] :
        ( r2_orders_2(sK4,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r2_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f166,f34])).

fof(f166,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ r2_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ r2_orders_2(sK3,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(resolution,[],[f155,f142])).

fof(f142,plain,(
    ! [X6,X7,X5] :
      ( r1_orders_2(X6,X5,X7)
      | ~ l1_orders_2(X6)
      | ~ r2_orders_2(X6,X5,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X6)) ) ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r1_orders_2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r2_orders_2(X4,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | sP1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f155,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK3,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f153,f94])).

fof(f153,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK3))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f151,f94])).

fof(f151,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK4))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f146,f35])).

fof(f146,plain,
    ( ! [X2,X3] :
        ( ~ l1_orders_2(sK4)
        | ~ m1_subset_1(X2,u1_struct_0(sK4))
        | r2_orders_2(sK4,X3,X2)
        | X2 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK4))
        | ~ m1_subset_1(X3,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ r1_orders_2(sK3,X3,X2) )
    | ~ spl9_5 ),
    inference(resolution,[],[f139,f138])).

fof(f210,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f208,f37])).

fof(f208,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f207,f94])).

fof(f207,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f206,f38])).

fof(f206,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f205,f94])).

fof(f205,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f204,f196])).

fof(f196,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f194,f42])).

fof(f194,plain,
    ( r2_orders_2(sK4,sK5,sK8)
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f63,f41])).

fof(f63,plain,
    ( r2_orders_2(sK4,sK7,sK8)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f204,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f201,f35])).

fof(f201,plain,
    ( ~ l1_orders_2(sK4)
    | ~ r2_orders_2(sK4,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl9_1 ),
    inference(resolution,[],[f198,f142])).

fof(f193,plain,
    ( spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f191,f37])).

fof(f191,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f190,f34])).

fof(f190,plain,
    ( ~ l1_orders_2(sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f185,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f140])).

% (28464)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (28466)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% (28464)Refutation not found, incomplete strategy% (28464)------------------------------
% (28464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28464)Termination reason: Refutation not found, incomplete strategy

% (28464)Memory used [KB]: 6140
% (28464)Time elapsed: 0.101 s
% (28464)------------------------------
% (28464)------------------------------
% (28469)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% (28478)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (28461)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (28462)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (28473)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f78,f56])).

fof(f56,plain,(
    ! [X2,X1] : ~ sP1(X1,X1,X2) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f185,plain,
    ( r2_orders_2(sK3,sK5,sK5)
    | spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f69,f183])).

fof(f183,plain,
    ( sK5 = sK6
    | spl9_2
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f182,f69])).

fof(f69,plain,
    ( r2_orders_2(sK3,sK5,sK6)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f92,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f90,f35])).

fof(f90,plain,
    ( ~ l1_orders_2(sK4)
    | spl9_4 ),
    inference(resolution,[],[f85,f45])).

fof(f85,plain,
    ( ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl9_4
  <=> m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f89,plain,
    ( ~ spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f79,f87,f83])).

fof(f79,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
      | u1_struct_0(sK4) = X0
      | ~ m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ) ),
    inference(superposition,[],[f54,f36])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f43,f67,f58])).

fof(f43,plain,
    ( r2_orders_2(sK3,sK5,sK6)
    | sP0(sK8,sK7,sK4,sK6,sK5,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f44,f62,f58])).

fof(f44,plain,
    ( ~ r2_orders_2(sK4,sK7,sK8)
    | sP0(sK8,sK7,sK4,sK6,sK5,sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:09:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (28468)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.45  % (28476)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.50  % (28477)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (28471)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (28479)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (28481)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (28463)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (28467)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (28460)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28463)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f65,f70,f89,f92,f193,f210,f219,f246,f270])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    ~spl9_1 | ~spl9_5 | ~spl9_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f269])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    $false | (~spl9_1 | ~spl9_5 | ~spl9_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f268,f247])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    r1_orders_2(sK3,sK5,sK5) | (~spl9_1 | ~spl9_6)),
% 0.21/0.51    inference(backward_demodulation,[],[f199,f218])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    sK5 = sK6 | ~spl9_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f216])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    spl9_6 <=> sK5 = sK6),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    r1_orders_2(sK3,sK5,sK6) | ~spl9_1),
% 0.21/0.51    inference(resolution,[],[f197,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5) | r1_orders_2(X5,X4,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((~r1_orders_2(X2,X1,X0) & r1_orders_2(X5,X4,X3)) | ~sP0(X0,X1,X2,X3,X4,X5))),
% 0.21/0.51    inference(rectify,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X5,X4,X1,X3,X2,X0] : ((~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3)) | ~sP0(X5,X4,X1,X3,X2,X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X5,X4,X1,X3,X2,X0] : ((~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3)) | ~sP0(X5,X4,X1,X3,X2,X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    sP0(sK6,sK5,sK4,sK6,sK5,sK3) | ~spl9_1),
% 0.21/0.51    inference(forward_demodulation,[],[f195,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    sK6 = sK8),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    (((((((~r2_orders_2(sK4,sK7,sK8) & r2_orders_2(sK3,sK5,sK6)) | sP0(sK8,sK7,sK4,sK6,sK5,sK3)) & sK6 = sK8 & sK5 = sK7 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK3))) & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & l1_orders_2(sK4)) & l1_orders_2(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f14,f25,f24,f23,f22,f21,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | sP0(X5,X4,X1,X3,X2,X0)) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(sK3,X2,X3)) | sP0(X5,X4,X1,X3,X2,sK3)) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,u1_struct_0(sK3))) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & l1_orders_2(X1)) & l1_orders_2(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(sK3,X2,X3)) | sP0(X5,X4,X1,X3,X2,sK3)) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,u1_struct_0(sK3))) & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(sK4,X4,X5) & r2_orders_2(sK3,X2,X3)) | sP0(X5,X4,sK4,X3,X2,sK3)) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,u1_struct_0(sK3))) & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4)) & l1_orders_2(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(sK4,X4,X5) & r2_orders_2(sK3,X2,X3)) | sP0(X5,X4,sK4,X3,X2,sK3)) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(X2,u1_struct_0(sK3))) => (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(sK4,X4,X5) & r2_orders_2(sK3,sK5,X3)) | sP0(X5,X4,sK4,X3,sK5,sK3)) & X3 = X5 & sK5 = X4 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(sK4,X4,X5) & r2_orders_2(sK3,sK5,X3)) | sP0(X5,X4,sK4,X3,sK5,sK3)) & X3 = X5 & sK5 = X4 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(X3,u1_struct_0(sK3))) => (? [X4] : (? [X5] : (((~r2_orders_2(sK4,X4,X5) & r2_orders_2(sK3,sK5,sK6)) | sP0(X5,X4,sK4,sK6,sK5,sK3)) & sK6 = X5 & sK5 = X4 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(sK4))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ? [X4] : (? [X5] : (((~r2_orders_2(sK4,X4,X5) & r2_orders_2(sK3,sK5,sK6)) | sP0(X5,X4,sK4,sK6,sK5,sK3)) & sK6 = X5 & sK5 = X4 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(X4,u1_struct_0(sK4))) => (? [X5] : (((~r2_orders_2(sK4,sK7,X5) & r2_orders_2(sK3,sK5,sK6)) | sP0(X5,sK7,sK4,sK6,sK5,sK3)) & sK6 = X5 & sK5 = sK7 & m1_subset_1(X5,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK4)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X5] : (((~r2_orders_2(sK4,sK7,X5) & r2_orders_2(sK3,sK5,sK6)) | sP0(X5,sK7,sK4,sK6,sK5,sK3)) & sK6 = X5 & sK5 = sK7 & m1_subset_1(X5,u1_struct_0(sK4))) => (((~r2_orders_2(sK4,sK7,sK8) & r2_orders_2(sK3,sK5,sK6)) | sP0(sK8,sK7,sK4,sK6,sK5,sK3)) & sK6 = sK8 & sK5 = sK7 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | sP0(X5,X4,X1,X3,X2,X0)) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.51    inference(definition_folding,[],[f8,f13])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (? [X4] : (? [X5] : ((((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & (X3 = X5 & X2 = X4)) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((X3 = X5 & X2 = X4) => ((r2_orders_2(X0,X2,X3) => r2_orders_2(X1,X4,X5)) & (r1_orders_2(X0,X2,X3) => r1_orders_2(X1,X4,X5)))))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((X3 = X5 & X2 = X4) => ((r2_orders_2(X0,X2,X3) => r2_orders_2(X1,X4,X5)) & (r1_orders_2(X0,X2,X3) => r1_orders_2(X1,X4,X5)))))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    sP0(sK8,sK5,sK4,sK6,sK5,sK3) | ~spl9_1),
% 0.21/0.51    inference(forward_demodulation,[],[f60,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    sK5 = sK7),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    sP0(sK8,sK7,sK4,sK6,sK5,sK3) | ~spl9_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    spl9_1 <=> sP0(sK8,sK7,sK4,sK6,sK5,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    ~r1_orders_2(sK3,sK5,sK5) | (~spl9_1 | ~spl9_5 | ~spl9_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f267,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_orders_2(sK3,sK5,sK5) | (~spl9_1 | ~spl9_5 | ~spl9_6)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f264])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r1_orders_2(sK3,sK5,sK5) | (~spl9_1 | ~spl9_5 | ~spl9_6)),
% 0.21/0.51    inference(resolution,[],[f249,f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r1_orders_2(sK4,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f136,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    l1_orders_2(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | r1_orders_2(sK4,X3,X2) | ~r1_orders_2(sK3,X3,X2) | ~l1_orders_2(sK3)) ) | ~spl9_5),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | r1_orders_2(sK4,X3,X2) | ~r1_orders_2(sK3,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~l1_orders_2(sK3)) ) | ~spl9_5),
% 0.21/0.51    inference(resolution,[],[f133,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r1_orders_2(sK4,X0,X1)) ) | ~spl9_5),
% 0.21/0.51    inference(forward_demodulation,[],[f132,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    u1_struct_0(sK3) = u1_struct_0(sK4) | ~spl9_5),
% 0.21/0.51    inference(equality_resolution,[],[f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | u1_struct_0(sK4) = X0) ) | ~spl9_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl9_5 <=> ! [X1,X0] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | u1_struct_0(sK4) = X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) | r1_orders_2(sK4,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK4))) ) | ~spl9_5),
% 0.21/0.51    inference(forward_demodulation,[],[f131,f94])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) | r1_orders_2(sK4,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4))) ) | ~spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    l1_orders_2(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) | r1_orders_2(sK4,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~m1_subset_1(X0,u1_struct_0(sK4)) | ~l1_orders_2(sK4)) ) | ~spl9_5),
% 0.21/0.51    inference(superposition,[],[f53,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    u1_orders_2(sK3) = u1_orders_2(sK4) | ~spl9_5),
% 0.21/0.51    inference(equality_resolution,[],[f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | u1_orders_2(sK4) = X1) ) | ~spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) | ~spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f35])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) | ~l1_orders_2(sK4) | ~spl9_5),
% 0.21/0.51    inference(superposition,[],[f45,f94])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | u1_orders_2(sK4) = X1 | ~m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))) ) | ~spl9_5),
% 0.21/0.51    inference(superposition,[],[f55,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK4)) | ~spl9_5),
% 0.21/0.51    inference(backward_demodulation,[],[f36,f94])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(sK4),u1_orders_2(sK4))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    ~r1_orders_2(sK4,sK5,sK5) | (~spl9_1 | ~spl9_6)),
% 0.21/0.51    inference(backward_demodulation,[],[f198,f218])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~r1_orders_2(sK4,sK5,sK6) | ~spl9_1),
% 0.21/0.51    inference(resolution,[],[f197,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3,X4,X5) | ~r1_orders_2(X2,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    spl9_6 | ~spl9_1 | spl9_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f245,f67,f58,f216])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl9_3 <=> r2_orders_2(sK3,sK5,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    sK5 = sK6 | (~spl9_1 | spl9_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f244,f37])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    sK5 = sK6 | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl9_1 | spl9_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f243,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~r2_orders_2(sK3,sK5,sK6) | spl9_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    r2_orders_2(sK3,sK5,sK6) | sK5 = sK6 | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f242,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ~m1_subset_1(sK6,u1_struct_0(sK3)) | r2_orders_2(sK3,sK5,sK6) | sK5 = sK6 | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f234,f34])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ~l1_orders_2(sK3) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | r2_orders_2(sK3,sK5,sK6) | sK5 = sK6 | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_1),
% 0.21/0.51    inference(resolution,[],[f199,f139])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X0,X2) | ~l1_orders_2(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | r2_orders_2(X1,X0,X2) | X0 = X2 | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.51    inference(resolution,[],[f77,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | X0 = X1 | ~r1_orders_2(X2,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | X0 = X1 | ~r1_orders_2(X2,X1,X0)) & ((X0 != X1 & r1_orders_2(X2,X1,X0)) | ~sP1(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP1(X2,X1,X0)))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP1(X2,X1,X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (sP1(X2,X1,X0) <=> (X1 != X2 & r1_orders_2(X0,X1,X2)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP1(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | r2_orders_2(X1,X2,X0)) )),
% 0.21/0.51    inference(resolution,[],[f51,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | r2_orders_2(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r2_orders_2(X0,X1,X2) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r2_orders_2(X0,X1,X2))) | ~sP2(X0,X1,X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_orders_2(X0,X1,X2) <=> sP1(X2,X1,X0)) | ~sP2(X0,X1,X2))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (sP2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(definition_folding,[],[f10,f16,f15])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    ~spl9_3 | spl9_6 | spl9_2 | ~spl9_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f182,f87,f62,f216,f67])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl9_2 <=> r2_orders_2(sK4,sK7,sK8)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    sK5 = sK6 | ~r2_orders_2(sK3,sK5,sK6) | (spl9_2 | ~spl9_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f181,f37])).
% 0.21/0.51  % (28470)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    sK5 = sK6 | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_orders_2(sK3,sK5,sK6) | (spl9_2 | ~spl9_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f178,f38])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~m1_subset_1(sK6,u1_struct_0(sK3)) | sK5 = sK6 | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~r2_orders_2(sK3,sK5,sK6) | (spl9_2 | ~spl9_5)),
% 0.21/0.51    inference(resolution,[],[f168,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~r2_orders_2(sK4,sK5,sK6) | spl9_2),
% 0.21/0.51    inference(forward_demodulation,[],[f73,f41])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~r2_orders_2(sK4,sK7,sK6) | spl9_2),
% 0.21/0.51    inference(forward_demodulation,[],[f64,f42])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~r2_orders_2(sK4,sK7,sK8) | spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r2_orders_2(sK4,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK3)) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r2_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f166,f34])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK3)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~r2_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK3)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~r2_orders_2(sK3,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X3,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.21/0.51    inference(resolution,[],[f155,f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X6,X7,X5] : (r1_orders_2(X6,X5,X7) | ~l1_orders_2(X6) | ~r2_orders_2(X6,X5,X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X6))) )),
% 0.21/0.51    inference(resolution,[],[f78,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r1_orders_2(X2,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (sP1(X3,X5,X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~r2_orders_2(X4,X5,X3) | ~m1_subset_1(X3,u1_struct_0(X4))) )),
% 0.21/0.51    inference(resolution,[],[f51,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | sP1(X2,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_orders_2(sK3,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK3)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(forward_demodulation,[],[f153,f94])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK3)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f152])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK3)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(forward_demodulation,[],[f151,f94])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK4)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(subsumption_resolution,[],[f146,f35])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~l1_orders_2(sK4) | ~m1_subset_1(X2,u1_struct_0(sK4)) | r2_orders_2(sK4,X3,X2) | X2 = X3 | ~m1_subset_1(X3,u1_struct_0(sK4)) | ~m1_subset_1(X3,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~r1_orders_2(sK3,X3,X2)) ) | ~spl9_5),
% 0.21/0.51    inference(resolution,[],[f139,f138])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~spl9_1 | ~spl9_2 | ~spl9_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    $false | (~spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f208,f37])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f207,f94])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK4)) | (~spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f206,f38])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | (~spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f205,f94])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    ~m1_subset_1(sK6,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | (~spl9_1 | ~spl9_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f204,f196])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    r2_orders_2(sK4,sK5,sK6) | ~spl9_2),
% 0.21/0.51    inference(forward_demodulation,[],[f194,f42])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    r2_orders_2(sK4,sK5,sK8) | ~spl9_2),
% 0.21/0.51    inference(forward_demodulation,[],[f63,f41])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    r2_orders_2(sK4,sK7,sK8) | ~spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ~r2_orders_2(sK4,sK5,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~spl9_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f201,f35])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ~l1_orders_2(sK4) | ~r2_orders_2(sK4,sK5,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~spl9_1),
% 0.21/0.51    inference(resolution,[],[f198,f142])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl9_2 | ~spl9_3 | ~spl9_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    $false | (spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f191,f37])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f190,f34])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~l1_orders_2(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.21/0.51    inference(resolution,[],[f185,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_orders_2(X1,X0,X0) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f140])).
% 0.21/0.52  % (28464)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (28466)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (28464)Refutation not found, incomplete strategy% (28464)------------------------------
% 0.21/0.52  % (28464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28464)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28464)Memory used [KB]: 6140
% 0.21/0.52  % (28464)Time elapsed: 0.101 s
% 0.21/0.52  % (28464)------------------------------
% 0.21/0.52  % (28464)------------------------------
% 0.21/0.52  % (28469)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (28478)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (28461)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (28462)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (28473)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.52    inference(resolution,[],[f78,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~sP1(X1,X1,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X0 != X1 | ~sP1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    r2_orders_2(sK3,sK5,sK5) | (spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f69,f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    sK5 = sK6 | (spl9_2 | ~spl9_3 | ~spl9_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f182,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    r2_orders_2(sK3,sK5,sK6) | ~spl9_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl9_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    $false | spl9_4),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f35])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~l1_orders_2(sK4) | spl9_4),
% 0.21/0.52    inference(resolution,[],[f85,f45])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ~m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) | spl9_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl9_4 <=> m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~spl9_4 | spl9_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f79,f87,f83])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) | u1_struct_0(sK4) = X0 | ~m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))) )),
% 0.21/0.52    inference(superposition,[],[f54,f36])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl9_1 | spl9_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f67,f58])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    r2_orders_2(sK3,sK5,sK6) | sP0(sK8,sK7,sK4,sK6,sK5,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl9_1 | ~spl9_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f62,f58])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~r2_orders_2(sK4,sK7,sK8) | sP0(sK8,sK7,sK4,sK6,sK5,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28463)------------------------------
% 0.21/0.52  % (28463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28463)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28463)Memory used [KB]: 6268
% 0.21/0.52  % (28463)Time elapsed: 0.107 s
% 0.21/0.52  % (28463)------------------------------
% 0.21/0.52  % (28463)------------------------------
% 0.21/0.53  % (28458)Success in time 0.169 s
%------------------------------------------------------------------------------
